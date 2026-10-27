module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCaseZeroIsom

public section

namespace CFSG.StandardType

section

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V] {m : ℕ}

private def ggCZProj (e : Fin m → V) (φ : Fin m → Module.Dual (ZMod p) V) (v : V) : V :=
  ∑ k, φ k v • e k

private lemma ggCZProj_apply (e : Fin m → V) (φ : Fin m → Module.Dual (ZMod p) V) (v : V) :
    ggCZProj e φ v = ∑ k, φ k v • e k :=
  rfl

private lemma ggCZProj_sub (e : Fin m → V) (φ : Fin m → Module.Dual (ZMod p) V) (x y : V) :
    ggCZProj e φ (x - y) = ggCZProj e φ x - ggCZProj e φ y := by
  have h : ∀ k : Fin m, φ k (x - y) • e k = φ k x • e k - φ k y • e k := by
    intro k
    rw [map_sub]
    exact sub_smul (φ k x) (φ k y) (e k)
  calc ggCZProj e φ (x - y) = ∑ k, (φ k x • e k - φ k y • e k) := by
        rw [ggCZProj_apply]
        exact Finset.sum_congr rfl fun k _ => h k
    _ = ggCZProj e φ x - ggCZProj e φ y := by
        rw [ggCZProj_apply, ggCZProj_apply]
        exact Finset.sum_sub_distrib (fun k => φ k x • e k) (fun k => φ k y • e k)

private lemma ggCZProj_smul (e : Fin m → V) (φ : Fin m → Module.Dual (ZMod p) V)
    (c : ZMod p) (x : V) : ggCZProj e φ (c • x) = c • ggCZProj e φ x := by
  have h : ∀ k : Fin m, φ k (c • x) • e k = c • (φ k x • e k) := by
    intro k
    rw [map_smul, smul_eq_mul]
    exact (smul_smul c (φ k x) (e k)).symm
  calc ggCZProj e φ (c • x) = ∑ k, c • (φ k x • e k) := by
        rw [ggCZProj_apply]
        exact Finset.sum_congr rfl fun k _ => h k
    _ = c • ggCZProj e φ x := by
        rw [ggCZProj_apply, Finset.smul_sum]

private lemma ggCZProj_apply_e {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) (i : Fin m) : ggCZProj e φ (e i) = e i := by
  rw [ggCZProj_apply, Finset.sum_eq_single i]
  · rw [hd i i, if_pos rfl, one_smul]
  · intro j _ hji
    rw [hd j i, if_neg hji, zero_smul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private lemma ggCZForm_sub_smul (φ : Fin m → Module.Dual (ZMod p) V) (a v : V) (c : ZMod p) :
    ggCZForm φ a (v - c • a) = ggCZForm φ a v - c * ggCZForm φ a a := by
  have h : ∀ k : Fin m, φ k a * φ k (v - c • a) =
      φ k a * φ k v - c * (φ k a * φ k a) := by
    intro k
    have h1 : φ k (v - c • a) = φ k v - φ k (c • a) :=
      LinearMap.map_sub (φ k) v (c • a)
    have h2 : φ k (c • a) = c • φ k a := LinearMap.map_smul (φ k) c a
    calc φ k a * φ k (v - c • a)
        = φ k a * (φ k v - φ k (c • a)) := congrArg (fun t => φ k a * t) h1
      _ = φ k a * (φ k v - c • φ k a) := congrArg (fun t => φ k a * (φ k v - t)) h2
      _ = φ k a * φ k v - c * (φ k a * φ k a) := by ring
  calc ggCZForm φ a (v - c • a)
      = ∑ k, (φ k a * φ k v - c * (φ k a * φ k a)) := by
        simp only [ggCZForm]
        exact Finset.sum_congr rfl fun k _ => h k
    _ = (∑ k, φ k a * φ k v) - ∑ k, c * (φ k a * φ k a) :=
        Finset.sum_sub_distrib (fun k => φ k a * φ k v)
          (fun k => c * (φ k a * φ k a))
    _ = (∑ k, φ k a * φ k v) - c * ∑ k, φ k a * φ k a := by rw [Finset.mul_sum]
    _ = ggCZForm φ a v - c * ggCZForm φ a a := rfl

private lemma ggCZProj_coord {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) (v : V) (k : Fin m) :
    φ k (∑ j, φ j v • e j) = φ k v := by
  rw [map_sum, Finset.sum_eq_single k]
  · rw [map_smul, hd k k, if_pos rfl, smul_eq_mul, mul_one]
  · intro j _ hjk
    rw [map_smul, hd k j, if_neg (Ne.symm hjk), smul_zero]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

private theorem ggCZ_linRefl_mem (hp2 : p ≠ 2) {e : Fin m → V}
    {φ : Fin m → Module.Dual (ZMod p) V} (hd : GGCZDual e φ) {t : V ≃ₗ[ZMod p] V} {a : V}
    {f : Module.Dual (ZMod p) V} (hfa : f a = 2) (hta : ∀ v, t v = v - f v • a)
    (hC : ∀ v, (∀ k, φ k v = 0) → t v = v)
    (hE : ∀ i, t (e i) = ∑ k, φ k (t (e i)) • e k) :
    a = ∑ k, φ k a • e k := by
  obtain ⟨ha0, hf0⟩ := ne_zero_of_apply_eq_two hp2 hfa
  have hfC : ∀ c : V, (∀ k, φ k c = 0) → f c = 0 := by
    intro c hc
    have h : c - f c • a = c := by
      rw [← hta c]
      exact hC c hc
    have h1 : f c • a = 0 := sub_eq_self.mp h
    rcases smul_eq_zero.mp h1 with h2 | h2
    · exact h2
    · exact absurd h2 ha0
  have hker : ∀ v : V, ∀ k, φ k (v - ∑ j, φ j v • e j) = 0 := by
    intro v k
    have h1 : φ k (v - ∑ j, φ j v • e j) = φ k v - φ k (∑ j, φ j v • e j) :=
      LinearMap.map_sub (φ k) v (∑ j, φ j v • e j)
    have h2 : φ k (∑ j, φ j v • e j) = φ k v := ggCZProj_coord hd v k
    exact h1.trans ((congrArg (fun x => φ k v - x) h2).trans (sub_self (φ k v)))
  have hf_decomp : ∀ v, f v = f (∑ j, φ j v • e j) := by
    intro v
    have h := hfC (v - ∑ j, φ j v • e j) (hker v)
    have h' : f v - f (∑ j, φ j v • e j) = 0 :=
      (LinearMap.map_sub f v (∑ j, φ j v • e j)).symm.trans h
    exact sub_eq_zero.mp h'
  have hf_eq : ∀ v, f v = ∑ k, φ k v * f (e k) := by
    intro v
    have hsum : f (∑ j, φ j v • e j) = ∑ j, φ j v * f (e j) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [map_smul, smul_eq_mul]
    exact (hf_decomp v).trans hsum
  have hex : ∃ i : Fin m, f (e i) ≠ 0 := by
    by_contra h
    have hzero : ∀ i, f (e i) = 0 := fun i => by
      by_contra hi
      exact h ⟨i, hi⟩
    have hfz : f = 0 := by
      ext v
      rw [hf_eq v]
      exact Finset.sum_eq_zero fun k _ => by rw [hzero k, mul_zero]
    exact hf0 hfz
  obtain ⟨i, hi⟩ := hex
  have ha_eq : a = (f (e i))⁻¹ • (e i - t (e i)) := by
    have h : e i - t (e i) = f (e i) • a := by
      rw [hta (e i)]
      abel
    have h' : (f (e i))⁻¹ • (e i - t (e i)) = (f (e i))⁻¹ • (f (e i) • a) :=
      congrArg (fun x => (f (e i))⁻¹ • x) h
    have h'' : (f (e i))⁻¹ • (f (e i) • a) = a :=
      (smul_smul (f (e i))⁻¹ (f (e i)) a).trans (by
        rw [inv_mul_cancel₀ hi, one_smul])
    exact (h'.trans h'').symm
  have hP_e : ggCZProj e φ (e i) = e i := ggCZProj_apply_e hd i
  have hP_t : ggCZProj e φ (t (e i)) = t (e i) :=
    (ggCZProj_apply e φ (t (e i))).trans (hE i).symm
  have hPa : ggCZProj e φ a = a := by
    calc ggCZProj e φ a
        = ggCZProj e φ ((f (e i))⁻¹ • (e i - t (e i))) :=
          congrArg (fun x => ggCZProj e φ x) ha_eq
      _ = (f (e i))⁻¹ • ggCZProj e φ (e i - t (e i)) :=
          ggCZProj_smul e φ ((f (e i))⁻¹) (e i - t (e i))
      _ = (f (e i))⁻¹ • (ggCZProj e φ (e i) - ggCZProj e φ (t (e i))) :=
          congrArg (fun x => (f (e i))⁻¹ • x) (ggCZProj_sub e φ (e i) (t (e i)))
      _ = (f (e i))⁻¹ • (e i - ggCZProj e φ (t (e i))) :=
          congrArg (fun x => (f (e i))⁻¹ • (x - ggCZProj e φ (t (e i)))) hP_e
      _ = (f (e i))⁻¹ • (e i - t (e i)) :=
          congrArg (fun x => (f (e i))⁻¹ • (e i - x)) hP_t
      _ = a := ha_eq.symm
  exact hPa.symm.trans (ggCZProj_apply e φ a)

private theorem ggCZ_linRefl_orth (hp2 : p ≠ 2) {e : Fin m → V}
    {φ : Fin m → Module.Dual (ZMod p) V} (hd : GGCZDual e φ) {t : V ≃ₗ[ZMod p] V} {a : V}
    {f : Module.Dual (ZMod p) V} (hfa : f a = 2) (hta : ∀ v, t v = v - f v • a)
    (hae : a = ∑ k, φ k a • e k)
    (hI : ∀ v w, ggCZForm φ (t v) (t w) = ggCZForm φ v w) :
    ggCZForm φ a a ≠ 0 ∧
      ∀ v, t v = v - (2 * ggCZForm φ v a / ggCZForm φ a a) • a := by
  obtain ⟨ha0, -⟩ := ne_zero_of_apply_eq_two hp2 hfa
  have hta_neg : t a = -a := by
    rw [hta a, hfa, two_smul]
    abel
  have hta_neg' : t a = (-1 : ZMod p) • a :=
    hta_neg.trans (neg_one_smul (ZMod p) a).symm
  have hB_ker : ∀ w, f w = 0 → ggCZForm φ a w = 0 := by
    intro w hw
    have htw : t w = w := by rw [hta w, hw, zero_smul, sub_zero]
    have h1 : ggCZForm φ (t a) (t w) = ggCZForm φ a w := hI a w
    have h1' : ggCZForm φ ((-1 : ZMod p) • a) w = ggCZForm φ a w := by
      calc ggCZForm φ ((-1 : ZMod p) • a) w = ggCZForm φ (t a) w :=
            congrArg (fun x => ggCZForm φ x w) hta_neg'.symm
        _ = ggCZForm φ (t a) (t w) :=
            (congrArg (fun x => ggCZForm φ (t a) x) htw).symm
        _ = ggCZForm φ a w := h1
    have h2 : (-1 : ZMod p) * ggCZForm φ a w = ggCZForm φ a w :=
      (ggCZForm_smul_left (-1) a w).symm.trans h1'
    have h3 : -ggCZForm φ a w = ggCZForm φ a w :=
      (neg_one_mul (ggCZForm φ a w)).symm.trans h2
    have h4 : ggCZForm φ a w + ggCZForm φ a w = 0 := neg_eq_iff_add_eq_zero.mp h3
    have h5 : (2 : ZMod p) * ggCZForm φ a w = 0 := by
      rw [two_mul]
      exact h4
    exact (mul_eq_zero.mp h5).resolve_left (zmod_two_ne_zero hp2)
  have hfw : ∀ v, f (v - (f v / 2) • a) = 0 := by
    intro v
    rw [map_sub, map_smul, hfa, smul_eq_mul,
      div_mul_cancel₀ (f v) (zmod_two_ne_zero hp2)]
    exact sub_self _
  have hB_all : ∀ v, ggCZForm φ a v = (f v / 2) * ggCZForm φ a a := by
    intro v
    have h0 : ggCZForm φ a (v - (f v / 2) • a) = 0 := hB_ker _ (hfw v)
    have h0' : ggCZForm φ a v - (f v / 2) * ggCZForm φ a a = 0 :=
      (ggCZForm_sub_smul φ a v (f v / 2)).symm.trans h0
    exact sub_eq_zero.mp h0'
  have hBaa : ggCZForm φ a a ≠ 0 := by
    intro h0
    have hBv : ∀ v, ggCZForm φ a v = 0 := by
      intro v
      have hv : ggCZForm φ a v = (f v / 2) * ggCZForm φ a a := hB_all v
      calc ggCZForm φ a v = (f v / 2) * ggCZForm φ a a := hv
        _ = (f v / 2) * 0 := congrArg (fun x => (f v / 2) * x) h0
        _ = 0 := mul_zero _
    have hphi : ∀ j, φ j a = 0 := by
      intro j
      have h := hBv (e j)
      exact ((ggCZForm_apply_e hd a j).symm).trans h
    have hsum : (∑ k, φ k a • e k) = 0 :=
      Finset.sum_eq_zero fun k _ => by rw [hphi k, zero_smul]
    exact ha0 (hae.trans hsum)
  have hfv : ∀ v, f v = 2 * ggCZForm φ a v / ggCZForm φ a a := by
    intro v
    have h2 : (2 : ZMod p) * ggCZForm φ a v = f v * ggCZForm φ a a := by
      rw [hB_all v, ← mul_assoc, mul_comm (2 : ZMod p) (f v / 2),
        div_mul_cancel₀ (f v) (zmod_two_ne_zero hp2)]
    rw [eq_div_iff hBaa]
    exact h2.symm
  exact ⟨hBaa, fun v => by rw [hta v, hfv v, ggCZForm_comm a v]⟩

theorem ggCZ_orth_of_isom [Finite V] (hp2 : p ≠ 2) {e : Fin m → V}
    {φ : Fin m → Module.Dual (ZMod p) V} (hd : GGCZDual e φ) {t : V ≃ₗ[ZMod p] V}
    (ht : GGLinRefl t) (hC : ∀ v, (∀ k, φ k v = 0) → t v = v)
    (hE : ∀ i, t (e i) = ∑ k, φ k (t (e i)) • e k)
    (hI : ∀ v w, ggCZForm φ (t v) (t w) = ggCZForm φ v w) :
    ∃ u : V, u = ∑ k, φ k u • e k ∧ ggCZForm φ u u ≠ 0 ∧
      ∀ v, t v = v - (2 * ggCZForm φ v u / ggCZForm φ u u) • u := by
  obtain ⟨a, f, hfa, hta⟩ := (ggDepA_linRefl_iff hp2 t).mp ht
  have hae := ggCZ_linRefl_mem hp2 hd hfa hta hC hE
  obtain ⟨hBaa, hform⟩ := ggCZ_linRefl_orth hp2 hd hfa hta hae hI
  exact ⟨a, hae, hBaa, hform⟩

theorem ggCZ_core_orth [Finite V] (hp2 : p ≠ 2) (hm : 3 ≤ m) {e : Fin m → V}
    {φ : Fin m → Module.Dual (ZMod p) V} (hd : GGCZDual e φ) {t : V ≃ₗ[ZMod p] V}
    (ht : GGLinRefl t) (hC : ∀ v, (∀ k, φ k v = 0) → t v = v)
    (hN : ∀ r ∈ ggCZRD e φ, t * r * t⁻¹ ∈ ggCZRD e φ) :
    ∃ u : V, u = ∑ k, φ k u • e k ∧ ggCZForm φ u u ≠ 0 ∧
      ∀ v, t v = v - (2 * ggCZForm φ v u / ggCZForm φ u u) • u := by
  obtain ⟨hE, hI⟩ := ggCZ_isom_of_normalizes hp2 hm hd ht hC hN
  exact ggCZ_orth_of_isom hp2 hd ht hC hE hI

end

end CFSG.StandardType

end
