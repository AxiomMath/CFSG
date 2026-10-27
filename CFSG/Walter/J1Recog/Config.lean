module

public import CFSG.Walter.J1Recog.Split
public import CFSG.Walter.J1Recog.Vals

public section

namespace CFSG.Walter.J1Recog

open CFSG.Walter.J1

namespace Setup

variable {G : Type} [Group G] [Finite G] (X : Setup G)

theorem not_inv_n_of_mem {v : G} (hv : v ∈ (X.S : Subgroup G)) : v * X.n * v⁻¹ ≠ X.n⁻¹ := by
  intro hvn
  have hv2 : v * v = 1 := X.mem_mul_self hv
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hmem : X.n⁻¹ * v * X.n ∈ (X.S : Subgroup G) := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ X.n_mem) v).mp hv
    rwa [inv_inv] at this
  have hn2 : X.n⁻¹ * v * X.n * v = X.n⁻¹ ^ 2 := by
    calc X.n⁻¹ * v * X.n * v = X.n⁻¹ * (v * X.n * v⁻¹) := by rw [hvinv]; group
      _ = X.n⁻¹ ^ 2 := by rw [hvn, pow_two]
  have hmem2 : X.n⁻¹ ^ 2 ∈ (X.S : Subgroup G) := by rw [← hn2]; exact Subgroup.mul_mem _ hmem hv
  have h4 : X.n ^ 4 = 1 := by
    have := X.mem_mul_self hmem2
    rw [← pow_add, inv_pow] at this
    exact inv_eq_one.mp this
  apply X.n_ne_one
  calc X.n = X.n ^ 8 * (X.n ^ 7)⁻¹ := by group
    _ = 1 := by rw [show (8 : ℕ) = 4 * 2 from rfl, pow_mul, h4, one_pow, X.n_pow_seven, inv_one,
      mul_one]

theorem not_mem_closure {s : G} (hs : orderOf s = 2) (hsn : s * X.n * s⁻¹ = X.n⁻¹) :
    s ∉ Subgroup.closure {X.t, X.n, X.m} := by
  intro hmem
  have hle : Subgroup.closure {X.t, X.n, X.m} ≤
      Subgroup.normalizer ((X.S : Subgroup G) : Set G) := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · exact Subgroup.le_normalizer X.t_mem
    · exact X.n_mem
    · exact X.m_mem
  exact X.not_inv_n_of_mem (JankoHyp.mem_sylow_of_orderOf_eq_two X.S (hle hmem) hs) hsn

omit [Finite G] in
theorem comm_eq_one {a b : G} (h : b * a = a * b) : b⁻¹ * a⁻¹ * b * a = 1 := by
  calc b⁻¹ * a⁻¹ * b * a = (a * b)⁻¹ * (b * a) := by group
    _ = 1 := by rw [h, inv_mul_cancel]

theorem hVals_eq_one : ∀ v ∈ hVals X.t X.n X.m, v = 1 := by
  have hte : ∀ i, X.t * X.e i = X.e i * X.t := fun i => (X.e_comm_t i).symm
  have he1 : X.n⁻¹ * X.t * X.n = X.e 1 := X.e1_eq.symm
  have he2 : (X.n ^ 2)⁻¹ * X.t * X.n ^ 2 = X.e 2 := rfl
  have htinv := X.h.t_inv
  simp only [hVals, List.mem_cons, List.not_mem_nil, or_false]
  rintro v (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · rw [pow_two, X.t_mul_t]
  · exact X.n_pow_seven
  · exact X.m_pow_three
  · rw [X.m_n, inv_pow, mul_inv_cancel]
  · exact comm_eq_one X.m_t.symm
  · rw [he1]; exact comm_eq_one (hte 1)
  · rw [he2]; exact comm_eq_one (hte 2)
  · have : X.n⁻¹ ^ 3 * X.t * X.n * X.t * X.n ^ 2 * X.t =
        (X.n ^ 3)⁻¹ * X.t * X.n ^ 3 * ((X.n ^ 2)⁻¹ * X.t * X.n ^ 2) * X.t := by group
    rw [this, he2, show (X.n ^ 3)⁻¹ * X.t * X.n ^ 3 = X.e 3 from rfl, ← X.rel03, X.e_zero,
      mul_assoc X.t, X.e_mul_self, mul_one, X.t_mul_t]
  · have : X.m⁻¹ * X.n⁻¹ * X.t * X.n * X.m * X.n⁻¹ ^ 2 * X.t * X.n ^ 2 =
        X.m⁻¹ * (X.n⁻¹ * X.t * X.n) * X.m * ((X.n ^ 2)⁻¹ * X.t * X.n ^ 2) := by group
    rw [this, he1, he2, X.m_e, X.e_mul_self]
  · have : X.m⁻¹ * X.n⁻¹ ^ 2 * X.t * X.n ^ 2 * X.m * X.n⁻¹ ^ 2 * X.t * X.n * X.t * X.n * X.t =
        X.m⁻¹ * ((X.n ^ 2)⁻¹ * X.t * X.n ^ 2) * X.m * ((X.n ^ 2)⁻¹ * X.t * X.n ^ 2) *
          (X.n⁻¹ * X.t * X.n) * X.t := by group
    rw [this, he1, he2, X.m_e]
    have h4 : X.e 4 = X.e 1 * (X.e 0 * X.e 2) := by
      have := X.rel_shift 1
      rw [← X.rel03] at this
      exact this.symm
    rw [show 2 * 2 = 4 from rfl, h4, ← X.e_zero]
    calc X.e 1 * (X.e 0 * X.e 2) * X.e 2 * X.e 1 * X.e 0 =
        X.e 1 * X.e 0 * (X.e 2 * X.e 2) * X.e 1 * X.e 0 := by group
      _ = 1 := by
        rw [X.e_mul_self, mul_one, mul_assoc (X.e 1), X.e_comm 0 1, ← mul_assoc, X.e_mul_self,
          one_mul, X.e_mul_self]

theorem ctVals_eq_one {x : G} (hpat : X.Pattern x) : ∀ v ∈ ctVals X.t X.n x, v = 1 := by
  have he5 : x * X.t * (X.n⁻¹ * X.t * X.n) = x * X.e 5 := by
    rw [← X.e1_eq, mul_assoc, ← X.e5_eq]
  have he3 : x * X.t * ((X.n ^ 2)⁻¹ * X.t * X.n ^ 2) = x * X.e 3 := by
    rw [mul_assoc, show (X.n ^ 2)⁻¹ * X.t * X.n ^ 2 = X.e 2 from rfl, ← X.rel03, X.e_zero]
  have he6 : x * (X.n⁻¹ * X.t * X.n) * ((X.n ^ 2)⁻¹ * X.t * X.n ^ 2) = x * X.e 6 := by
    rw [← X.e1_eq, mul_assoc, show (X.n ^ 2)⁻¹ * X.t * X.n ^ 2 = X.e 2 from rfl, X.rel06]
  simp only [ctVals, List.mem_cons, List.not_mem_nil, or_false]
  rintro v (rfl | rfl | rfl)
  · rw [he5]; exact hpat.1.1
  · rw [he3]; exact hpat.2.1.1
  · rw [he6]; exact hpat.2.2.1.1

theorem p1Vals_eq_one {s u : G} (hs : orderOf s = 2) (hsn : s * X.n * s⁻¹ = X.n⁻¹)
    (hsm : s * X.m = X.m * s) (hu : orderOf u = 2) (hut : u * X.t = X.t * u)
    (hus : u * s = s * u) (hum : u * X.m * u⁻¹ = X.m⁻¹) :
    ∀ v ∈ p1Vals X.t X.n X.m s u, v = 1 := by
  have hst : s ≠ X.t := by rintro rfl; exact X.t_not_inv_n hsn
  have hs2 : s * s = 1 := (orderOf_eq_two_iff.mp hs).1
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hu2 : u * u = 1 := (orderOf_eq_two_iff.mp hu).1
  simp only [p1Vals, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro v (hv | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact X.hVals_eq_one v hv
  · rw [pow_two, hs2]
  · exact comm_eq_one hsm
  · rw [pow_two]
    calc s * X.n * (s * X.n) = (s * X.n * s⁻¹) * X.n := by rw [hsinv]; group
      _ = 1 := by rw [hsn, inv_mul_cancel]
  · exact (X.pow_five hs hsm hst).1
  · rw [pow_two, hu2]
  · have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
    rw [pow_two]
    calc u * X.m * (u * X.m) = (u * X.m * u⁻¹) * X.m := by rw [huinv]; group
      _ = 1 := by rw [hum, inv_mul_cancel]
  · exact comm_eq_one hut
  · exact comm_eq_one hus

theorem dvd_card_closure {s u : G} (hs : orderOf s = 2) (hsn : s * X.n * s⁻¹ = X.n⁻¹)
    (hsm : s * X.m = X.m * s) :
    840 ∣ Nat.card (Subgroup.closure (Set.range ![X.t, X.n, X.m, s, u])) := by
  set K := Subgroup.closure (Set.range ![X.t, X.n, X.m, s, u])
  have hst : s ≠ X.t := by rintro rfl; exact X.t_not_inv_n hsn
  have htK : X.t ∈ K := Subgroup.subset_closure ⟨0, rfl⟩
  have hnK : X.n ∈ K := Subgroup.subset_closure ⟨1, rfl⟩
  have hmK : X.m ∈ K := Subgroup.subset_closure ⟨2, rfl⟩
  have hsK : s ∈ K := Subgroup.subset_closure ⟨3, rfl⟩
  have hSK : (X.S : Subgroup G) ≤ K := by
    intro v hv
    rcases X.isCoord.cover hv with rfl | ⟨i, -, rfl⟩
    · exact K.one_mem
    · exact K.mul_mem (K.mul_mem (K.inv_mem (K.pow_mem hnK i)) htK) (K.pow_mem hnK i)
  have h8 : 8 ∣ Nat.card K := X.h.card_sylow' X.S ▸ Subgroup.card_dvd_of_le hSK
  have h3 : 3 ∣ Nat.card K := X.orderOf_m ▸ Subgroup.orderOf_dvd_natCard K hmK
  have h7 : 7 ∣ Nat.card K := X.orderOf_n ▸ Subgroup.orderOf_dvd_natCard K hnK
  have h5 : 5 ∣ Nat.card K := by
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨h5, h1⟩ := X.pow_five hs hsm hst
    have := Subgroup.orderOf_dvd_natCard K (K.mul_mem htK hsK)
    rwa [orderOf_eq_prime h5 h1] at this
  have h24 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 8 3) h8 h3
  have h120 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 24 5) h24 h5
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 120 7) h120 h7

end Setup

theorem exists_config {G : Type} [Group G] [Finite G] (h : JankoHyp G) :
    ∃ c : Case, ∃ f : Fin 5 → G, (∀ w ∈ rels c, ev f w = 1) ∧
      f 3 ∉ Subgroup.closure {f 0, f 1, f 2} ∧
      840 ∣ Nat.card (Subgroup.closure (Set.range f)) := by
  obtain ⟨X⟩ := exists_setup h
  obtain ⟨s, u, x, hs, hsn, hsm, hu, hut, hus, hum, hxF, hxu, hpat⟩ := X.exists_gens
  have hP1 := X.p1Vals_eq_one hs hsn hsm hu hut hus hum
  have hCT := X.ctVals_eq_one hpat
  have hnot := X.not_mem_closure hs hsn
  have h840 := X.dvd_card_closure (u := u) hs hsn hsm
  have key : ∀ c : Case, (c = .O1a ∨ c = .O1b → x = u) → (c = .O2a ∨ c = .O2b → x = X.t * u) →
      extraVal c X.t X.n X.m u = 1 →
      ∃ c : Case, ∃ f : Fin 5 → G, (∀ w ∈ rels c, ev f w = 1) ∧
        f 3 ∉ Subgroup.closure {f 0, f 1, f 2} ∧
        840 ∣ Nat.card (Subgroup.closure (Set.range f)) := by
    intro c h1 h2 hextra
    refine ⟨c, ![X.t, X.n, X.m, s, u], ?_, hnot, h840⟩
    rw [forall_ev_rels_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
    intro v hv
    simp only [relVals, List.mem_append, List.mem_singleton] at hv
    rcases hv with (hv | hv) | rfl
    · exact hP1 v hv
    · cases c with
      | O1a => rw [← h1 (Or.inl rfl)] at hv; exact hCT v hv
      | O1b => rw [← h1 (Or.inr rfl)] at hv; exact hCT v hv
      | O2a => rw [← h2 (Or.inl rfl)] at hv; exact hCT v hv
      | O2b => rw [← h2 (Or.inr rfl)] at hv; exact hCT v hv
    · exact hextra
  rcases hxu with rfl | rfl
  · rcases X.split_O1 hs hsn hsm hu hut hus hum hxF hpat with h | h
    · exact key .O1a (fun _ => rfl) (by simp) (Setup.comm_eq_one h)
    · exact key .O1b (fun _ => rfl) (by simp) (Setup.comm_eq_one h)
  · rcases X.split_O2 hs hsn hsm hu hut hus hum hxF hpat with h | h
    · exact key .O2a (by simp) (fun _ => rfl) (Setup.comm_eq_one h)
    · exact key .O2b (by simp) (fun _ => rfl) (Setup.comm_eq_one h)

end CFSG.Walter.J1Recog
