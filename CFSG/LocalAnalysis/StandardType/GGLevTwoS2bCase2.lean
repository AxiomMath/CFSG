module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2bCover2

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin

theorem levTwoS2b_exists_ne_two (n : ℕ) (hn : 3 ≤ n) (a k : Fin n) :
    ∃ c : Fin n, c ≠ a ∧ c ≠ k := by
  have hssub : ({a, k} : Finset (Fin n)) ⊂ Finset.univ := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.subset_univ _, ?_⟩
    intro hEq
    have hle : n ≤ 2 := by
      calc n = (Finset.univ : Finset (Fin n)).card := by simp
        _ = ({a, k} : Finset (Fin n)).card := by rw [hEq]
        _ ≤ 2 := Finset.card_insert_le _ _
    omega
  obtain ⟨c, -, hc⟩ := Finset.exists_of_ssubset hssub
  rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  exact ⟨c, hc.1, hc.2⟩

theorem levTwoS2b_inC1_shape {n : ℕ} {k : Fin n} {x : Fin n → ℤ}
    (hx : levTwoS2b_isShort n x) (hxk : levTwoS2b_coord n x k = 0) :
    ∃ a : Fin n, a ≠ k ∧ ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      x = levTwoS2b_ofCoord n (Pi.single a s) := by
  obtain ⟨a, s, hs, hcx⟩ := hx
  refine ⟨a, ?_, s, hs, ?_⟩
  · intro h
    have hzero : s = 0 := by
      have hk' := hxk
      rw [hcx, h, Pi.single_eq_same] at hk'
      exact hk'
    rcases hs with h1 | h1 <;> simp [h1] at hzero
  · apply levTwoS2b_coord_injective n
    rw [levTwoS2b_coord_ofCoord, hcx]

theorem levTwoS2b_inC2_shape {n : ℕ} {k : Fin n} {x : Fin n → ℤ}
    (hx : levTwoS2b_isShort n x) (hxk : levTwoS2b_coord n x k ≠ 0) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ x = levTwoS2b_ofCoord n (Pi.single k s) := by
  obtain ⟨a, s, hs, hcx⟩ := hx
  have hak : a = k := by
    by_contra h
    exact hxk (by rw [hcx]; simp [Ne.symm h])
  refine ⟨s, hs, ?_⟩
  rw [← hak]
  apply levTwoS2b_coord_injective n
  rw [levTwoS2b_coord_ofCoord, hcx]

theorem levTwoS2b_inC3_shape {n : ℕ} {k : Fin n} {x : Fin n → ℤ}
    (hx : levTwoS2b_isLong n x) (hxk : levTwoS2b_coord n x k ≠ 0) :
    ∃ a : Fin n, a ≠ k ∧ ∃ s t : ℤ, (s = 1 ∨ s = -1) ∧ (t = 1 ∨ t = -1) ∧
      x = levTwoS2b_ofCoord n (Pi.single a s + Pi.single k t) := by
  obtain ⟨a, b, s, t, hab, hs, ht, hcx⟩ := hx
  have hkb : b = k ∨ a = k := by
    by_contra h
    push Not at h
    exact hxk (by rw [hcx]; simp [Pi.add_apply, h.1, h.2])
  rcases hkb with hbk | hak
  · refine ⟨a, ?_, s, t, hs, ht, ?_⟩
    · rw [← hbk]; exact hab
    · rw [← hbk]; apply levTwoS2b_coord_injective n
      rw [levTwoS2b_coord_ofCoord, hcx]
  · refine ⟨b, ?_, t, s, ht, hs, ?_⟩
    · rw [← hak]; exact Ne.symm hab
    · rw [← hak]; apply levTwoS2b_coord_injective n
      rw [levTwoS2b_coord_ofCoord, hcx, add_comm]

theorem levTwoS2b_cl_insert_of_mem {n : ℕ} {S : Set (Fin n → ℤ)} {y : Fin n → ℤ}
    (hy : Cl (isFiniteType_cartanB n) S y) :
    Cl (isFiniteType_cartanB n) (S ∪ {y}) = Cl (isFiniteType_cartanB n) S := by
  apply le_antisymm
  · intro z hz
    induction hz with
    | base hb =>
        rcases hb with hbS | hby
        · exact Cl.base hbS
        · rw [Set.mem_singleton_iff] at hby; subst hby; exact hy
    | refl ha hb iha ihb => exact Cl.refl iha ihb
  · intro z hz
    exact levTwoS2b_cl_mono (isFiniteType_cartanB n) (fun z hz => Or.inl hz) hz

theorem levTwoS2b_tcRoot_case2 (n : ℕ) (hn : 2 ≤ n) (p : ℕ) (_hp : p.Prime) (_hp2 : p ≠ 2)
    (c : Fin n → ZMod p) (k : Fin n) (h3 : 3 ≤ n - 1) (_hk : levTwoS2b_D c k ≠ 0)
    (_hZ : ∀ a : Fin n, a ≠ k → levTwoS2b_D c a = 0) :
    TCRoot (isFiniteType_cartanB n) (levTwoS2b_PhiCase2 n k) := by
  intro S hS
  classical
  have hn1 : 1 ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  have transfer : ∀ {T : Set (Fin n → ℤ)}, levTwoS2b_PhiCase2 n k ⊆ T →
      ∀ {y x : Fin n → ℤ}, Cl (isFiniteType_cartanB n) T y →
      Cl (isFiniteType_cartanB n) (levTwoS2b_PhiCase2 n k ∪ {y}) x →
      Cl (isFiniteType_cartanB n) T x := by
    intro T hPhiT y x hy hx
    have hsub : levTwoS2b_PhiCase2 n k ∪ ({y} : Set (Fin n → ℤ)) ⊆ T ∪ {y} := by
      intro z hz
      rcases hz with hz | hz
      · exact Or.inl (hPhiT hz)
      · exact Or.inr hz
    have h1 := levTwoS2b_cl_mono (isFiniteType_cartanB n) hsub hx
    rwa [levTwoS2b_cl_insert_of_mem hy] at h1
  by_cases hC3 : ∃ x ∈ S, levTwoS2b_isLong n x ∧ levTwoS2b_coord n x k ≠ 0
  · by_cases hC1 : ∃ x ∈ S, levTwoS2b_isShort n x ∧ levTwoS2b_coord n x k = 0
    ·
      obtain ⟨x1, hx1S, hx1s, hx1k⟩ := hC1
      obtain ⟨x3, hx3S, hx3l, hx3k⟩ := hC3
      obtain ⟨a1, ha1k, s1, hs1, hx1eq⟩ := levTwoS2b_inC1_shape hx1s hx1k
      obtain ⟨a3, ha3k, s3, t3, hs3, ht3, hx3eq⟩ := levTwoS2b_inC3_shape hx3l hx3k
      obtain ⟨c3, hc3a, hc3k⟩ := levTwoS2b_exists_ne_two n hn3 a3 k
      refine ⟨{x1, x3}, ?_, by have h := Finset.card_insert_le x1 ({x3} : Finset (Fin n → ℤ)); rw [Finset.card_singleton] at h; omega, ?_⟩
      · intro y hy
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact hx1S
        · exact hx3S
      · apply levTwoS2b_cl_eq_of_subset (isFiniteType_cartanB n)
        · intro y hy
          simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl
          · exact hx1S
          · exact hx3S
        · intro y hyS
          have hPhiT : levTwoS2b_PhiCase2 n k ⊆
              levTwoS2b_PhiCase2 n k ∪ (↑({x1, x3} : Finset (Fin n → ℤ)) : Set (Fin n → ℤ)) := fun z hz => Or.inl hz
          have hx1rep : Cl (isFiniteType_cartanB n)
              (levTwoS2b_PhiCase2 n k ∪ (↑({x1, x3} : Finset (Fin n → ℤ)) : Set (Fin n → ℤ))) x1 :=
            Cl.base (Or.inr (by simp))
          have hx3rep : Cl (isFiniteType_cartanB n)
              (levTwoS2b_PhiCase2 n k ∪ (↑({x1, x3} : Finset (Fin n → ℤ)) : Set (Fin n → ℤ))) x3 :=
            Cl.base (Or.inr (by simp))
          have hC1rep : Cl (isFiniteType_cartanB n)
              (levTwoS2b_PhiCase2 n k ∪ (↑({x1, x3} : Finset (Fin n → ℤ)) : Set (Fin n → ℤ)))
              (levTwoS2b_ofCoord n (Pi.single a1 s1)) := by
            rw [← hx1eq]; exact hx1rep
          have hC3rep : Cl (isFiniteType_cartanB n)
              (levTwoS2b_PhiCase2 n k ∪ (↑({x1, x3} : Finset (Fin n → ℤ)) : Set (Fin n → ℤ)))
              (levTwoS2b_ofCoord n (Pi.single a3 s3 + Pi.single k t3)) := by
            rw [← hx3eq]; exact hx3rep
          rcases levTwoS2b_isShort_or_isLong n (hS y hyS) with hys | hyl
          · by_cases hyk : levTwoS2b_coord n y k = 0
            · obtain ⟨ay, hayk, sy, hsy, hyeq⟩ := levTwoS2b_inC1_shape hys hyk
              rw [hyeq]
              exact transfer hPhiT hC1rep
                (levTwoS2b_case2_C1_all' n hn1 k ha1k hs1 hayk hsy)
            · obtain ⟨sy, hsy, hyeq⟩ := levTwoS2b_inC2_shape hys hyk
              rw [hyeq]
              have hC1aligned : Cl (isFiniteType_cartanB n)
                  (levTwoS2b_PhiCase2 n k ∪ (↑({x1, x3} : Finset (Fin n → ℤ)) : Set (Fin n → ℤ)))
                  (levTwoS2b_ofCoord n (Pi.single a3 s3)) :=
                transfer hPhiT hC1rep
                  (levTwoS2b_case2_C1_all' n hn1 k ha1k hs1 ha3k hs3)
              have hC2rep : Cl (isFiniteType_cartanB n)
                  (levTwoS2b_PhiCase2 n k ∪ (↑({x1, x3} : Finset (Fin n → ℤ)) : Set (Fin n → ℤ)))
                  (levTwoS2b_ofCoord n (Pi.single k (-t3))) := by
                have hcl : Cl (isFiniteType_cartanB n)
                    (levTwoS2b_PhiCase2 n k ∪ (↑({x1, x3} : Finset (Fin n → ℤ)) : Set (Fin n → ℤ)))
                    (weylAction (isFiniteType_cartanB n)
                      (rRefl (isFiniteType_cartanB n)
                        (levTwoS2b_ofCoord n (Pi.single a3 s3 + Pi.single k t3)))
                      (levTwoS2b_ofCoord n (Pi.single a3 s3))) := by
                  rw [← hx3eq]
                  exact Cl.refl hx3rep hC1aligned
                rwa [levTwoS2b_rRefl_pair n hn1 ha3k hs3 ht3] at hcl
              exact transfer hPhiT hC2rep
                (levTwoS2b_case2_C2_all n hn1 k
                  (by rcases ht3 with h | h <;> simp [h]) hsy)
          · by_cases hyk : levTwoS2b_coord n y k = 0
            · exact Cl.base (hPhiT ⟨hS y hyS, hyl, hyk⟩)
            · obtain ⟨ay, hayk, sy, ty, hsy, hty, hyeq⟩ := levTwoS2b_inC3_shape hyl hyk
              rw [hyeq]
              exact transfer hPhiT hC3rep
                (levTwoS2b_case2_C3_all' n hn1 k ha3k hc3a hc3k hayk hs3 ht3 hsy hty)
    · by_cases hC2 : ∃ x ∈ S, levTwoS2b_isShort n x ∧ levTwoS2b_coord n x k ≠ 0
      ·
        obtain ⟨x2, hx2S, hx2s, hx2k⟩ := hC2
        obtain ⟨x3, hx3S, hx3l, hx3k⟩ := hC3
        obtain ⟨s2, hs2, hx2eq⟩ := levTwoS2b_inC2_shape hx2s hx2k
        obtain ⟨a3, ha3k, s3, t3, hs3, ht3, hx3eq⟩ := levTwoS2b_inC3_shape hx3l hx3k
        obtain ⟨c3, hc3a, hc3k⟩ := levTwoS2b_exists_ne_two n hn3 a3 k
        refine ⟨{x2, x3}, ?_, by have h := Finset.card_insert_le x2 ({x3} : Finset (Fin n → ℤ)); rw [Finset.card_singleton] at h; omega, ?_⟩
        · intro y hy
          simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl
          · exact hx2S
          · exact hx3S
        · apply levTwoS2b_cl_eq_of_subset (isFiniteType_cartanB n)
          · intro y hy
            simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl
            · exact hx2S
            · exact hx3S
          · intro y hyS
            have hPhiT : levTwoS2b_PhiCase2 n k ⊆
                levTwoS2b_PhiCase2 n k ∪ (↑({x2, x3} : Finset (Fin n → ℤ)) : Set (Fin n → ℤ)) := fun z hz => Or.inl hz
            have hx2rep : Cl (isFiniteType_cartanB n)
                (levTwoS2b_PhiCase2 n k ∪ (↑({x2, x3} : Finset (Fin n → ℤ)) : Set (Fin n → ℤ))) x2 :=
              Cl.base (Or.inr (by simp))
            have hx3rep : Cl (isFiniteType_cartanB n)
                (levTwoS2b_PhiCase2 n k ∪ (↑({x2, x3} : Finset (Fin n → ℤ)) : Set (Fin n → ℤ))) x3 :=
              Cl.base (Or.inr (by simp))
            have hC2rep : Cl (isFiniteType_cartanB n)
                (levTwoS2b_PhiCase2 n k ∪ (↑({x2, x3} : Finset (Fin n → ℤ)) : Set (Fin n → ℤ)))
                (levTwoS2b_ofCoord n (Pi.single k s2)) := by
              rw [← hx2eq]; exact hx2rep
            have hC3rep : Cl (isFiniteType_cartanB n)
                (levTwoS2b_PhiCase2 n k ∪ (↑({x2, x3} : Finset (Fin n → ℤ)) : Set (Fin n → ℤ)))
                (levTwoS2b_ofCoord n (Pi.single a3 s3 + Pi.single k t3)) := by
              rw [← hx3eq]; exact hx3rep
            rcases levTwoS2b_isShort_or_isLong n (hS y hyS) with hys | hyl
            · by_cases hyk : levTwoS2b_coord n y k = 0
              · obtain ⟨ay, hayk, sy, hsy, hyeq⟩ := levTwoS2b_inC1_shape hys hyk
                rw [hyeq]
                have hC2aligned : Cl (isFiniteType_cartanB n)
                    (levTwoS2b_PhiCase2 n k ∪ (↑({x2, x3} : Finset (Fin n → ℤ)) : Set (Fin n → ℤ)))
                    (levTwoS2b_ofCoord n (Pi.single k t3)) :=
                  transfer hPhiT hC2rep
                    (levTwoS2b_case2_C2_all n hn1 k hs2 ht3)
                have hC1rep : Cl (isFiniteType_cartanB n)
                    (levTwoS2b_PhiCase2 n k ∪ (↑({x2, x3} : Finset (Fin n → ℤ)) : Set (Fin n → ℤ)))
                    (levTwoS2b_ofCoord n (Pi.single a3 (-s3))) := by
                  have hcl : Cl (isFiniteType_cartanB n)
                      (levTwoS2b_PhiCase2 n k ∪ (↑({x2, x3} : Finset (Fin n → ℤ)) : Set (Fin n → ℤ)))
                      (weylAction (isFiniteType_cartanB n)
                        (rRefl (isFiniteType_cartanB n)
                          (levTwoS2b_ofCoord n (Pi.single a3 s3 + Pi.single k t3)))
                        (levTwoS2b_ofCoord n (Pi.single k t3))) := by
                    rw [← hx3eq]
                    exact Cl.refl hx3rep hC2aligned
                  rwa [levTwoS2b_rRefl_pair' n hn1 ha3k hs3 ht3] at hcl
                exact transfer hPhiT hC1rep
                  (levTwoS2b_case2_C1_all' n hn1 k ha3k
                    (by rcases hs3 with h | h <;> simp [h]) hayk hsy)
              · obtain ⟨sy, hsy, hyeq⟩ := levTwoS2b_inC2_shape hys hyk
                rw [hyeq]
                exact transfer hPhiT hC2rep
                  (levTwoS2b_case2_C2_all n hn1 k hs2 hsy)
            · by_cases hyk : levTwoS2b_coord n y k = 0
              · exact Cl.base (hPhiT ⟨hS y hyS, hyl, hyk⟩)
              · obtain ⟨ay, hayk, sy, ty, hsy, hty, hyeq⟩ := levTwoS2b_inC3_shape hyl hyk
                rw [hyeq]
                exact transfer hPhiT hC3rep
                  (levTwoS2b_case2_C3_all' n hn1 k ha3k hc3a hc3k hayk hs3 ht3 hsy hty)
      ·
        obtain ⟨x3, hx3S, hx3l, hx3k⟩ := hC3
        obtain ⟨a3, ha3k, s3, t3, hs3, ht3, hx3eq⟩ := levTwoS2b_inC3_shape hx3l hx3k
        obtain ⟨c3, hc3a, hc3k⟩ := levTwoS2b_exists_ne_two n hn3 a3 k
        refine ⟨{x3}, ?_, by simp, ?_⟩
        · intro y hy
          simp only [Finset.mem_coe, Finset.mem_singleton] at hy
          subst hy
          exact hx3S
        · apply levTwoS2b_cl_eq_of_subset (isFiniteType_cartanB n)
          · intro y hy
            simp only [Finset.mem_coe, Finset.mem_singleton] at hy
            subst hy
            exact hx3S
          · intro y hyS
            have hPhiT : levTwoS2b_PhiCase2 n k ⊆
                levTwoS2b_PhiCase2 n k ∪ (↑({x3} : Finset (Fin n → ℤ)) : Set (Fin n → ℤ)) := fun z hz => Or.inl hz
            have hC3rep : Cl (isFiniteType_cartanB n)
                (levTwoS2b_PhiCase2 n k ∪ (↑({x3} : Finset (Fin n → ℤ)) : Set (Fin n → ℤ)))
                (levTwoS2b_ofCoord n (Pi.single a3 s3 + Pi.single k t3)) := by
              rw [← hx3eq]; exact Cl.base (Or.inr (by simp))
            rcases levTwoS2b_isShort_or_isLong n (hS y hyS) with hys | hyl
            · exact absurd ⟨y, hyS, hys, by
                by_cases hyk : levTwoS2b_coord n y k = 0
                · exact hyk
                · exact absurd ⟨y, hyS, hys, hyk⟩ hC2⟩ hC1
            · by_cases hyk : levTwoS2b_coord n y k = 0
              · exact Cl.base (hPhiT ⟨hS y hyS, hyl, hyk⟩)
              · obtain ⟨ay, hayk, sy, ty, hsy, hty, hyeq⟩ := levTwoS2b_inC3_shape hyl hyk
                rw [hyeq]
                exact transfer hPhiT hC3rep
                  (levTwoS2b_case2_C3_all' n hn1 k ha3k hc3a hc3k hayk hs3 ht3 hsy hty)
  · by_cases hC1 : ∃ x ∈ S, levTwoS2b_isShort n x ∧ levTwoS2b_coord n x k = 0
    · by_cases hC2 : ∃ x ∈ S, levTwoS2b_isShort n x ∧ levTwoS2b_coord n x k ≠ 0
      ·
        obtain ⟨x1, hx1S, hx1s, hx1k⟩ := hC1
        obtain ⟨x2, hx2S, hx2s, hx2k⟩ := hC2
        obtain ⟨a1, ha1k, s1, hs1, hx1eq⟩ := levTwoS2b_inC1_shape hx1s hx1k
        obtain ⟨s2, hs2, hx2eq⟩ := levTwoS2b_inC2_shape hx2s hx2k
        refine ⟨{x1, x2}, ?_, by have h := Finset.card_insert_le x1 ({x2} : Finset (Fin n → ℤ)); rw [Finset.card_singleton] at h; omega, ?_⟩
        · intro y hy
          simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl
          · exact hx1S
          · exact hx2S
        · apply levTwoS2b_cl_eq_of_subset (isFiniteType_cartanB n)
          · intro y hy
            simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl
            · exact hx1S
            · exact hx2S
          · intro y hyS
            have hPhiT : levTwoS2b_PhiCase2 n k ⊆
                levTwoS2b_PhiCase2 n k ∪ (↑({x1, x2} : Finset (Fin n → ℤ)) : Set (Fin n → ℤ)) := fun z hz => Or.inl hz
            have hC1rep : Cl (isFiniteType_cartanB n)
                (levTwoS2b_PhiCase2 n k ∪ (↑({x1, x2} : Finset (Fin n → ℤ)) : Set (Fin n → ℤ)))
                (levTwoS2b_ofCoord n (Pi.single a1 s1)) := by
              rw [← hx1eq]; exact Cl.base (Or.inr (by simp))
            have hC2rep : Cl (isFiniteType_cartanB n)
                (levTwoS2b_PhiCase2 n k ∪ (↑({x1, x2} : Finset (Fin n → ℤ)) : Set (Fin n → ℤ)))
                (levTwoS2b_ofCoord n (Pi.single k s2)) := by
              rw [← hx2eq]
              exact Cl.base (Or.inr (by simp))
            rcases levTwoS2b_isShort_or_isLong n (hS y hyS) with hys | hyl
            · by_cases hyk : levTwoS2b_coord n y k = 0
              · obtain ⟨ay, hayk, sy, hsy, hyeq⟩ := levTwoS2b_inC1_shape hys hyk
                rw [hyeq]
                exact transfer hPhiT hC1rep
                  (levTwoS2b_case2_C1_all' n hn1 k ha1k hs1 hayk hsy)
              · obtain ⟨sy, hsy, hyeq⟩ := levTwoS2b_inC2_shape hys hyk
                rw [hyeq]
                exact transfer hPhiT hC2rep
                  (levTwoS2b_case2_C2_all n hn1 k hs2 hsy)
            · have hyk : levTwoS2b_coord n y k = 0 := by
                by_contra h
                exact hC3 ⟨y, hyS, hyl, h⟩
              exact Cl.base (hPhiT ⟨hS y hyS, hyl, hyk⟩)
      ·
        obtain ⟨x1, hx1S, hx1s, hx1k⟩ := hC1
        obtain ⟨a1, ha1k, s1, hs1, hx1eq⟩ := levTwoS2b_inC1_shape hx1s hx1k
        refine ⟨{x1}, ?_, by simp, ?_⟩
        · intro y hy
          simp only [Finset.mem_coe, Finset.mem_singleton] at hy
          subst hy
          exact hx1S
        · apply levTwoS2b_cl_eq_of_subset (isFiniteType_cartanB n)
          · intro y hy
            simp only [Finset.mem_coe, Finset.mem_singleton] at hy
            subst hy
            exact hx1S
          · intro y hyS
            have hPhiT : levTwoS2b_PhiCase2 n k ⊆
                levTwoS2b_PhiCase2 n k ∪ (↑({x1} : Finset (Fin n → ℤ)) : Set (Fin n → ℤ)) := fun z hz => Or.inl hz
            have hC1rep : Cl (isFiniteType_cartanB n)
                (levTwoS2b_PhiCase2 n k ∪ (↑({x1} : Finset (Fin n → ℤ)) : Set (Fin n → ℤ)))
                (levTwoS2b_ofCoord n (Pi.single a1 s1)) := by
              rw [← hx1eq]; exact Cl.base (Or.inr (by simp))
            rcases levTwoS2b_isShort_or_isLong n (hS y hyS) with hys | hyl
            · by_cases hyk : levTwoS2b_coord n y k = 0
              · obtain ⟨ay, hayk, sy, hsy, hyeq⟩ := levTwoS2b_inC1_shape hys hyk
                rw [hyeq]
                exact transfer hPhiT hC1rep
                  (levTwoS2b_case2_C1_all' n hn1 k ha1k hs1 hayk hsy)
              · exact absurd ⟨y, hyS, hys, hyk⟩ hC2
            · have hyk : levTwoS2b_coord n y k = 0 := by
                by_contra h
                exact hC3 ⟨y, hyS, hyl, h⟩
              exact Cl.base (hPhiT ⟨hS y hyS, hyl, hyk⟩)
    · by_cases hC2 : ∃ x ∈ S, levTwoS2b_isShort n x ∧ levTwoS2b_coord n x k ≠ 0
      ·
        obtain ⟨x2, hx2S, hx2s, hx2k⟩ := hC2
        obtain ⟨s2, hs2, hx2eq⟩ := levTwoS2b_inC2_shape hx2s hx2k
        refine ⟨{x2}, ?_, by simp, ?_⟩
        · intro y hy
          simp only [Finset.mem_coe, Finset.mem_singleton] at hy
          subst hy
          exact hx2S
        · apply levTwoS2b_cl_eq_of_subset (isFiniteType_cartanB n)
          · intro y hy
            simp only [Finset.mem_coe, Finset.mem_singleton] at hy
            subst hy
            exact hx2S
          · intro y hyS
            have hPhiT : levTwoS2b_PhiCase2 n k ⊆
                levTwoS2b_PhiCase2 n k ∪ (↑({x2} : Finset (Fin n → ℤ)) : Set (Fin n → ℤ)) := fun z hz => Or.inl hz
            have hC2rep : Cl (isFiniteType_cartanB n)
                (levTwoS2b_PhiCase2 n k ∪ (↑({x2} : Finset (Fin n → ℤ)) : Set (Fin n → ℤ)))
                (levTwoS2b_ofCoord n (Pi.single k s2)) := by
              rw [← hx2eq]; exact Cl.base (Or.inr (by simp))
            rcases levTwoS2b_isShort_or_isLong n (hS y hyS) with hys | hyl
            · by_cases hyk : levTwoS2b_coord n y k = 0
              · exact absurd ⟨y, hyS, hys, hyk⟩ hC1
              · obtain ⟨sy, hsy, hyeq⟩ := levTwoS2b_inC2_shape hys hyk
                rw [hyeq]
                exact transfer hPhiT hC2rep
                  (levTwoS2b_case2_C2_all n hn1 k hs2 hsy)
            · have hyk : levTwoS2b_coord n y k = 0 := by
                by_contra h
                exact hC3 ⟨y, hyS, hyl, h⟩
              exact Cl.base (hPhiT ⟨hS y hyS, hyl, hyk⟩)
      ·
        refine ⟨∅, by simp, by simp, ?_⟩
        apply levTwoS2b_cl_eq_of_subset (isFiniteType_cartanB n)
        · simp
        · intro y hyS
          rcases levTwoS2b_isShort_or_isLong n (hS y hyS) with hys | hyl
          · exact absurd ⟨y, hyS, hys, by
              by_cases hyk : levTwoS2b_coord n y k = 0
              · exact hyk
              · exact absurd ⟨y, hyS, hys, hyk⟩ hC2⟩ hC1
          · have hyk : levTwoS2b_coord n y k = 0 := by
              by_contra h
              exact hC3 ⟨y, hyS, hyl, h⟩
            exact Cl.base (Or.inl ⟨hS y hyS, hyl, hyk⟩)




end CFSG.StandardType.LevTwo
