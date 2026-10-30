module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829S9Mat
public import CFSG.Quasithin.Vol2.Ch8Sec2L829S9Chain3
public import CFSG.Quasithin.Vol2.Ch8Sec2L829LN1

public section

namespace CFSG.Quasithin.H13.L829N

open Matrix
open scoped MatrixGroups

theorem s9c_part1 {E : Type} [Field E] [Finite E] [CharP E 2] {d : ℕ}
    (t : GL (Fin d) E) (ht : IsTransvectionK t)
    (K₀ : Subgroup (GL (Fin d) E)) (htK : ∀ k ∈ K₀, t * k * t⁻¹ ∈ K₀)
    (hK₀N : K₀ ≤ Subgroup.closure {x | ∃ k ∈ K₀, x = k * t * k⁻¹}) :
    ∃ N : Subgroup (GL (Fin d) E), N = Subgroup.closure {x | ∃ k ∈ K₀, x = k * t * k⁻¹} ∧
      K₀ ≤ N ∧ t ∈ N ∧ (∀ g ∈ N, ∀ k ∈ K₀, g * k * g⁻¹ ∈ K₀ ∧ g⁻¹ * k * g ∈ K₀) := by
  classical
  have hFin : Finite (GL (Fin d) E) := inferInstance
  obtain ⟨N, hN⟩ : ∃ N : Subgroup (GL (Fin d) E),
      N = Subgroup.closure {x | ∃ k ∈ K₀, x = k * t * k⁻¹} := ⟨_, rfl⟩
  have hKN : K₀ ≤ N := hN ▸ hK₀N
  have hgenN : ∀ k ∈ K₀, k * t * k⁻¹ ∈ N := fun k hk => by
    rw [hN]; exact Subgroup.subset_closure ⟨k, hk, rfl⟩
  have htN : t ∈ N := by simpa using hgenN 1 K₀.one_mem
  have htK' : ∀ k ∈ K₀, t⁻¹ * k * t ∈ K₀ := by
    intro k hk
    let c : K₀ → K₀ := fun y => ⟨t * y * t⁻¹, htK y y.2⟩
    have hc : Function.Injective c := by
      intro y z hyz
      apply Subtype.ext
      have h := congrArg Subtype.val hyz
      simpa [c] using h
    obtain ⟨y, hy⟩ := Finite.injective_iff_surjective.mp hc ⟨k, hk⟩
    have hk' : t * (y : GL (Fin d) E) * t⁻¹ = k := congrArg Subtype.val hy
    have e : t⁻¹ * k * t = (y : GL (Fin d) E) := by
      rw [← hk']; group
    rw [e]
    exact y.2
  have hcjK : ∀ a ∈ K₀, ∀ k ∈ K₀, a * k * a⁻¹ ∈ K₀ := fun a ha k hk =>
    K₀.mul_mem (K₀.mul_mem ha hk) (K₀.inv_mem ha)
  have hcjK' : ∀ a ∈ K₀, ∀ k ∈ K₀, a⁻¹ * k * a ∈ K₀ := fun a ha k hk =>
    K₀.mul_mem (K₀.mul_mem (K₀.inv_mem ha) hk) ha
  have hP : ∀ g ∈ N, (∀ k ∈ K₀, g * k * g⁻¹ ∈ K₀) ∧ (∀ k ∈ K₀, g⁻¹ * k * g ∈ K₀) := by
    intro g hg
    have hg' := hg
    rw [hN] at hg'
    clear hg
    induction hg' using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      constructor
      · intro k hk
        have e : (a * t * a⁻¹) * k * (a * t * a⁻¹)⁻¹ = a * (t * (a⁻¹ * k * a) * t⁻¹) * a⁻¹ := by
          group
        rw [e]
        exact hcjK a ha _ (htK _ (hcjK' a ha k hk))
      · intro k hk
        have e : (a * t * a⁻¹)⁻¹ * k * (a * t * a⁻¹) = a * (t⁻¹ * (a⁻¹ * k * a) * t) * a⁻¹ := by
          group
        rw [e]
        exact hcjK a ha _ (htK' _ (hcjK' a ha k hk))
    | one => exact ⟨fun k hk => by simpa using hk, fun k hk => by simpa using hk⟩
    | mul x y hxm hym hx hy =>
      constructor
      · intro k hk
        have e : x * y * k * (x * y)⁻¹ = x * (y * k * y⁻¹) * x⁻¹ := by group
        rw [e]
        exact hx.1 _ (hy.1 k hk)
      · intro k hk
        have e : (x * y)⁻¹ * k * (x * y) = y⁻¹ * (x⁻¹ * k * x) * y := by group
        rw [e]
        exact hy.2 _ (hx.2 k hk)
    | inv x hxm hx => exact ⟨hx.2, hx.1⟩
  have hnorm : ∀ g ∈ N, ∀ k ∈ K₀, g * k * g⁻¹ ∈ K₀ ∧ g⁻¹ * k * g ∈ K₀ := fun g hg k hk =>
    ⟨(hP g hg).1 k hk, (hP g hg).2 k hk⟩
  exact ⟨N, hN, hKN, htN, hnorm⟩

theorem s9c_part2 {E : Type} [Field E] [Finite E] [CharP E 2] {d : ℕ}
    (t : GL (Fin d) E) (ht : IsTransvectionK t) (N : Subgroup (GL (Fin d) E)) :
    ∃ r : ℕ, ∃ Y : ℕ → Submodule E (Fin d → E), Y 0 = ⊥ ∧ Y r = ⊤ ∧
      (∀ i j, i ≤ j → j ≤ r → Y i ≤ Y j) ∧
      (∀ i, i ≤ r → S9cInv N (Y i)) ∧
      (∀ i, i < r → Y i < Y (i + 1) ∧
        ∀ W : Submodule E (Fin d → E), S9cInv N W → Y i ≤ W → W ≤ Y (i + 1) →
          W = Y i ∨ W = Y (i + 1)) ∧
      (∃ u : Fin d → E, u ≠ 0 ∧ ∀ v : Fin d → E, ∃ c : E,
          ((t : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ v - v = c • u) := by
  classical
  have hTop : S9cInv N (⊤ : Submodule E (Fin d → E)) := fun _ _ _ _ => Submodule.mem_top
  obtain ⟨r, Y, hY0, hYr, hmono, hYinv, hstep⟩ := s9c_chain_exists N ⊤ hTop
  have hrank : (((t : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) - 1).rank = 1 := by
    unfold IsTransvectionK at ht
    exact ht.2.2
  obtain ⟨u, hu0, hucov⟩ := s9c_rank_one_vec hrank
  refine ⟨r, Y, hY0, hYr, hmono, hYinv, hstep, ⟨u, hu0, fun v => ?_⟩⟩
  obtain ⟨c, hc⟩ := hucov v
  exact ⟨c, by rw [← hc, Matrix.sub_mulVec, Matrix.one_mulVec]⟩

theorem s9c_nontriv_line {E : Type} [Field E] {d r : ℕ} (N : Subgroup (GL (Fin d) E))
    (t : GL (Fin d) E) (htN : t ∈ N) (Y : ℕ → Submodule E (Fin d → E))
    (hYinv : ∀ i, i ≤ r → S9cInv N (Y i)) (u : Fin d → E)
    (hcov : ∀ v : Fin d → E, ∃ c : E,
      ((t : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ v - v = c • u)
    (i : ℕ) (hi : i < r)
    (hI : ∃ v ∈ Y (i + 1), ((t : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ v - v ∉ Y i) :
    u ∈ Y (i + 1) ∧ u ∉ Y i := by
  obtain ⟨v, hv, hnot⟩ := hI
  obtain ⟨c, hc⟩ := hcov v
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hnot
    rw [hc, zero_smul]
    exact (Y i).zero_mem
  have htv : ((t : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ v - v ∈ Y (i + 1) :=
    Submodule.sub_mem _ (hYinv (i + 1) (Nat.succ_le_of_lt hi) t htN v hv) hv
  rw [hc] at htv
  have hu : u ∈ Y (i + 1) := by
    have h := Submodule.smul_mem _ c⁻¹ htv
    rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at h
  refine ⟨hu, fun hui => hnot ?_⟩
  rw [hc]
  exact Submodule.smul_mem _ c hui

theorem s9c_nontriv_unique {E : Type} [Field E] {d r : ℕ} (t : GL (Fin d) E)
    (Y : ℕ → Submodule E (Fin d → E)) (hmono : ∀ i j, i ≤ j → j ≤ r → Y i ≤ Y j)
    (u : Fin d → E)
    (hline : ∀ i, i < r → (∃ v ∈ Y (i + 1), ((t : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ v - v ∉ Y i) →
      u ∈ Y (i + 1) ∧ u ∉ Y i)
    (i j : ℕ) (hi : i < r) (hj : j < r)
    (hI : ∃ v ∈ Y (i + 1), ((t : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ v - v ∉ Y i)
    (hJ : ∃ v ∈ Y (j + 1), ((t : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ v - v ∉ Y j) :
    i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact (hline j hj hJ).2 (hmono (i + 1) j h hj.le (hline i hi hI).1)
  · exact (hline i hi hI).2 (hmono (j + 1) i h hi.le (hline j hj hJ).1)

theorem s9c_triv_prop {E : Type} [Field E] {d r : ℕ} (K₀ N : Subgroup (GL (Fin d) E))
    (t : GL (Fin d) E)
    (hN : N = Subgroup.closure {x | ∃ k ∈ K₀, x = k * t * k⁻¹}) (hKN : K₀ ≤ N)
    (Y : ℕ → Submodule E (Fin d → E)) (hYinv : ∀ i, i ≤ r → S9cInv N (Y i)) (i : ℕ) (hi : i < r)
    (htriv : ∀ v ∈ Y (i + 1), ((t : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ v - v ∈ Y i)
    (g : GL (Fin d) E) (hg : g ∈ N) :
    ∀ v ∈ Y (i + 1), ((g : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ v - v ∈ Y i := by
  have hg' := hg
  rw [hN] at hg'
  clear hg
  induction hg' using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    intro v hv
    have hkN : k ∈ N := hKN hk
    have hw : ((k⁻¹ : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ v ∈ Y (i + 1) :=
      hYinv (i + 1) (Nat.succ_le_of_lt hi) k⁻¹ (N.inv_mem hkN) v hv
    have hw' := htriv _ hw
    have hk' := hYinv i hi.le k hkN _ hw'
    have e : ((k * t * k⁻¹ : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ v - v =
        ((k : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ
          (((t : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ
            ((k⁻¹ : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ v -
            ((k⁻¹ : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ v) := by
      simp only [Units.val_mul, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Units.mul_inv,
        Matrix.one_mulVec, mul_assoc]
    rw [e]
    exact hk'
  | one =>
    intro v hv
    simp
  | mul x y hxm hym hx hy =>
    intro v hv
    have hxN : x ∈ N := by rw [hN]; exact hxm
    have e : ((x * y : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ v - v =
        ((x : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ
          (((y : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ v - v) +
        (((x : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ v - v) := by
      simp only [Units.val_mul, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
      abel
    rw [e]
    exact Submodule.add_mem _ (hYinv i hi.le x hxN _ (hy v hv)) (hx v hv)
  | inv x hxm hx =>
    intro v hv
    have hxN : x ∈ N := by rw [hN]; exact hxm
    have e : ((x⁻¹ : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ v - v =
        -(((x⁻¹ : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ
          (((x : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ v - v)) := by
      simp only [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      abel
    rw [e]
    exact Submodule.neg_mem _ (hYinv i hi.le _ (N.inv_mem hxN) _ (hx v hv))

theorem s9c_K0_nontrivial {E : Type} [Field E] [CharP E 2] {d : ℕ}
    (t : GL (Fin d) E) (ht : IsTransvectionK t)
    (K₀ N : Subgroup (GL (Fin d) E)) (hN : N = Subgroup.closure {x | ∃ k ∈ K₀, x = k * t * k⁻¹})
    (hKN : K₀ ≤ N) (htN : t ∈ N)
    {A B : Submodule E (Fin d → E)} (hA : S9cInv N A) (hB : S9cInv N B) (hAB : A ≤ B)
    (hirr : ∀ W : Submodule E (Fin d → E), S9cInv N W → A ≤ W → W ≤ B → W = A ∨ W = B)
    (hnt : ∃ v ∈ B, ((t : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ v - v ∉ A) :
    ∃ x : K₀, s9cRep hA hB ⟨(x : GL (Fin d) E), hKN x.2⟩ ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have hk1 : ∀ k (hk : k ∈ K₀), s9cRep hA hB ⟨k, hKN hk⟩ = 1 := fun k hk => hcon ⟨k, hk⟩
  have hcomm : ∀ g ∈ Subgroup.closure {x | ∃ k ∈ K₀, x = k * t * k⁻¹},
      ∃ hgN : g ∈ N, Commute (s9cRep hA hB ⟨g, hgN⟩) (s9cRep hA hB ⟨t, htN⟩) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      have hxN : k * t * k⁻¹ ∈ N := by rw [hN]; exact Subgroup.subset_closure ⟨k, hk, rfl⟩
      refine ⟨hxN, ?_⟩
      have e : (⟨k * t * k⁻¹, hxN⟩ : N) = ⟨k, hKN hk⟩ * ⟨t, htN⟩ * ⟨k, hKN hk⟩⁻¹ := by
        apply Subtype.ext
        simp [mul_assoc]
      rw [e, map_mul, map_mul, map_inv, hk1 k hk]
      simp [Commute, SemiconjBy]
    | one =>
      refine ⟨N.one_mem, ?_⟩
      have e : (⟨1, N.one_mem⟩ : N) = 1 := rfl
      rw [e, map_one]
      exact Commute.one_left _
    | mul x y _ _ hx hy =>
      obtain ⟨h1, c1⟩ := hx
      obtain ⟨h2, c2⟩ := hy
      refine ⟨N.mul_mem h1 h2, ?_⟩
      have e : (⟨x * y, N.mul_mem h1 h2⟩ : N) = ⟨x, h1⟩ * ⟨y, h2⟩ := rfl
      rw [e, map_mul]
      exact c1.mul_left c2
    | inv x _ hx =>
      obtain ⟨h1, c1⟩ := hx
      refine ⟨N.inv_mem h1, ?_⟩
      have e : (⟨x⁻¹, N.inv_mem h1⟩ : N) = ⟨x, h1⟩⁻¹ := rfl
      rw [e, map_inv]
      exact c1.inv_left
  set T := s9cIndHom (s9cOfN hA hB ⟨t, htN⟩) with hTdef
  have hcommEnd : ∀ g : N,
      s9cIndHom (s9cOfN hA hB g) * T = T * s9cIndHom (s9cOfN hA hB g) := by
    intro g
    obtain ⟨_, c⟩ := hcomm g.1 (by rw [← hN]; exact g.2)
    have c' : s9cRep hA hB g * s9cRep hA hB ⟨t, htN⟩ = s9cRep hA hB ⟨t, htN⟩ * s9cRep hA hB g := c
    have key := congrArg Units.val c'
    rw [Units.val_mul, Units.val_mul, s9cRep_val, s9cRep_val] at key
    apply (LinearMap.toMatrix (Module.finBasis E (s9cSub A B))
      (Module.finBasis E (s9cSub A B))).injective
    rw [LinearMap.toMatrix_mul, LinearMap.toMatrix_mul]
    exact key
  have hWinv : ∀ g : N, ∀ w ∈ LinearMap.ker (T - 1),
      s9cIndHom (s9cOfN hA hB g) w ∈ LinearMap.ker (T - 1) := by
    intro g w hw
    rw [LinearMap.mem_ker] at hw ⊢
    have h1 : T (s9cIndHom (s9cOfN hA hB g) w) = s9cIndHom (s9cOfN hA hB g) (T w) := by
      have := congrArg (fun F => F w) (hcommEnd g)
      simpa [Module.End.mul_apply] using this.symm
    have hTw : T w = w := by
      simpa [LinearMap.sub_apply, sub_eq_zero] using hw
    simp [LinearMap.sub_apply, h1, hTw]
  have hirrW := s9c_subq_irred hA hB hAB hirr (LinearMap.ker (T - 1)) hWinv
  have hT1 : T - 1 ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hvA⟩ := hnt
    have hfix : T (s9cMk v hv) = s9cMk v hv := by
      have h2 := congrArg (fun F => F (s9cMk v hv)) h0
      simpa [LinearMap.sub_apply, sub_eq_zero] using h2
    rw [hTdef, s9cIndHom_mk] at hfix
    have hq := (Submodule.Quotient.eq _).mp hfix
    apply hvA
    simpa [s9cFlag, s9cOfN] using hq
  have hsq : (T - 1) * (T - 1) = 0 := by
    have hG : (s9cOfN hA hB ⟨t, htN⟩ - 1) * (s9cOfN hA hB ⟨t, htN⟩ - 1) = 0 := by
      apply Subtype.ext
      unfold IsTransvectionK at ht
      simpa [s9cOfN] using ht.2.1
    have e1 : T - 1 = s9cIndHom (s9cOfN hA hB ⟨t, htN⟩ - 1) := by
      rw [map_sub, map_one]
    rw [e1, ← map_mul, hG, map_zero]
  rcases hirrW with hbot | htop
  · apply hT1
    apply LinearMap.ext
    intro w
    have hz : (T - 1) ((T - 1) w) = 0 := by
      have := congrArg (fun F => F w) hsq
      simpa [Module.End.mul_apply] using this
    have hmem : (T - 1) w ∈ LinearMap.ker (T - 1) := LinearMap.mem_ker.mpr hz
    rw [hbot, Submodule.mem_bot] at hmem
    simpa using hmem
  · apply hT1
    apply LinearMap.ext
    intro w
    have hmem : w ∈ LinearMap.ker (T - 1) := by rw [htop]; exact Submodule.mem_top
    simpa using hmem

theorem s9c_gen_range {E : Type} [Field E] {d : ℕ} (t : GL (Fin d) E) (K₀ N : Subgroup (GL (Fin d) E))
    (hN : N = Subgroup.closure {x | ∃ k ∈ K₀, x = k * t * k⁻¹}) (hKN : K₀ ≤ N) (htN : t ∈ N)
    {A B : Submodule E (Fin d → E)} (hA : S9cInv N A) (hB : S9cInv N B) :
    (s9cRep hA hB).range = Subgroup.closure
      {s | ∃ x ∈ (s9cRep hA hB).range, s = x * s9cRep hA hB ⟨t, htN⟩ * x⁻¹} := by
  classical
  apply le_antisymm
  · have key : ∀ g ∈ Subgroup.closure {x : GL (Fin d) E | ∃ k ∈ K₀, x = k * t * k⁻¹},
        ∃ hgN : g ∈ N, s9cRep hA hB ⟨g, hgN⟩ ∈ Subgroup.closure
          {s | ∃ x ∈ (s9cRep hA hB).range, s = x * s9cRep hA hB ⟨t, htN⟩ * x⁻¹} := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨k, hk, rfl⟩ := hx
        have hxN : k * t * k⁻¹ ∈ N := by rw [hN]; exact Subgroup.subset_closure ⟨k, hk, rfl⟩
        refine ⟨hxN, Subgroup.subset_closure ⟨s9cRep hA hB ⟨k, hKN hk⟩, ⟨⟨k, hKN hk⟩, rfl⟩, ?_⟩⟩
        have e : (⟨k * t * k⁻¹, hxN⟩ : N) = ⟨k, hKN hk⟩ * ⟨t, htN⟩ * ⟨k, hKN hk⟩⁻¹ := by
          apply Subtype.ext
          simp [mul_assoc]
        rw [e, map_mul, map_mul, map_inv]
      | one =>
        refine ⟨N.one_mem, ?_⟩
        have e : (⟨1, N.one_mem⟩ : N) = 1 := rfl
        rw [e, map_one]
        exact Subgroup.one_mem _
      | mul x y _ _ hx hy =>
        obtain ⟨h1, c1⟩ := hx
        obtain ⟨h2, c2⟩ := hy
        refine ⟨N.mul_mem h1 h2, ?_⟩
        have e : (⟨x * y, N.mul_mem h1 h2⟩ : N) = ⟨x, h1⟩ * ⟨y, h2⟩ := rfl
        rw [e, map_mul]
        exact Subgroup.mul_mem _ c1 c2
      | inv x _ hx =>
        obtain ⟨h1, c1⟩ := hx
        refine ⟨N.inv_mem h1, ?_⟩
        have e : (⟨x⁻¹, N.inv_mem h1⟩ : N) = ⟨x, h1⟩⁻¹ := rfl
        rw [e, map_inv]
        exact Subgroup.inv_mem _ c1
    rintro g ⟨h, rfl⟩
    obtain ⟨_, hC⟩ := key h.1 (by rw [← hN]; exact h.2)
    exact hC
  · rw [Subgroup.closure_le]
    rintro s ⟨x, hx, rfl⟩
    have hτ : s9cRep hA hB ⟨t, htN⟩ ∈ (s9cRep hA hB).range := MonoidHom.mem_range.mpr ⟨⟨t, htN⟩, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hτ) (Subgroup.inv_mem _ hx)

theorem s9c_irred_range {E : Type} [Field E] {d : ℕ} {N : Subgroup (GL (Fin d) E)}
    {A B : Submodule E (Fin d → E)} (hA : S9cInv N A) (hB : S9cInv N B) (hAB : A ≤ B)
    (hstep : ∀ W : Submodule E (Fin d → E), S9cInv N W → A ≤ W → W ≤ B → W = A ∨ W = B)
    (W : Submodule E (Fin (Module.finrank E (s9cSub A B)) → E))
    (hW : ∀ g ∈ (s9cRep hA hB).range, ∀ w ∈ W,
      ((g : GL (Fin (Module.finrank E (s9cSub A B))) E) : Matrix _ _ E) *ᵥ w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  let e : s9cSub A B ≃ₗ[E] (Fin (Module.finrank E (s9cSub A B)) → E) :=
    (Module.finBasis E (s9cSub A B)).equivFun
  let W' : Submodule E (s9cSub A B) := W.comap e.toLinearMap
  have hW' : ∀ g : N, ∀ w ∈ W', s9cIndHom (s9cOfN hA hB g) w ∈ W' := by
    intro g w hw
    have hmem : s9cRep hA hB g ∈ (s9cRep hA hB).range := ⟨g, rfl⟩
    have key : e (s9cIndHom (s9cOfN hA hB g) w) =
        ((s9cRep hA hB g : GL (Fin (Module.finrank E (s9cSub A B))) E) :
          Matrix _ _ E) *ᵥ e w := by
      rw [s9cRep_val, Module.Basis.equivFun_apply, Module.Basis.equivFun_apply]
      exact (LinearMap.toMatrix_mulVec_repr (Module.finBasis E (s9cSub A B)) (Module.finBasis E (s9cSub A B)) _ _).symm
    show e (s9cIndHom (s9cOfN hA hB g) w) ∈ W
    rw [key]
    exact hW _ hmem _ hw
  rcases s9c_subq_irred hA hB hAB hstep W' hW' with h | h
  · left
    rw [eq_bot_iff]
    intro w hw
    have hx : e.symm w ∈ W' := by
      show e (e.symm w) ∈ W
      rw [LinearEquiv.apply_symm_apply]
      exact hw
    rw [h, Submodule.mem_bot] at hx
    rw [Submodule.mem_bot]
    calc w = e (e.symm w) := (e.apply_symm_apply w).symm
      _ = 0 := by rw [hx, map_zero]
  · right
    rw [eq_top_iff]
    intro w _
    have hx : e.symm w ∈ W' := by rw [h]; exact Submodule.mem_top
    have hx' : e (e.symm w) ∈ W := hx
    rwa [LinearEquiv.apply_symm_apply] at hx'

theorem s9c_cf_of_quot {K₀ Ks : Type} [Group K₀] [Group Ks] {n : ℕ} {E : Type} [Field E]
    (σ : K₀ →* Ks) (hσ : Function.Surjective σ) (hKs : IsSimpleGroup Ks)
    (ρK : K₀ →* GL (Fin n) E) (hker : ρK.ker ≤ σ.ker)
    (N' : Subgroup (GL (Fin n) E)) (hle : ρK.range ≤ N')
    (hnorm : ∀ g ∈ N', ∀ k ∈ ρK.range, g * k * g⁻¹ ∈ ρK.range) :
    E1.IsCompositionFactor ↥N' Ks := by
  classical
  have hnormal : ((ρK.range).subgroupOf N').Normal := by
    constructor
    intro a ha g
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    have := hnorm g.1 g.2 a ha
    simpa using this
  have hsub : ((ρK.range).subgroupOf N').IsSubnormal := Subgroup.Normal.isSubnormal hnormal
  let σ'' : K₀ ⧸ ρK.ker →* Ks := QuotientGroup.lift ρK.ker σ hker
  let σbar : ↥ρK.range →* Ks := σ''.comp (QuotientGroup.quotientKerEquivRange ρK).symm.toMonoidHom
  have hσbar : Function.Surjective σbar := by
    intro s
    obtain ⟨x, rfl⟩ := hσ s
    refine ⟨(QuotientGroup.quotientKerEquivRange ρK) (QuotientGroup.mk x), ?_⟩
    simp [σbar, σ'']
  let ψ : ↥((ρK.range).subgroupOf N') →* Ks :=
    σbar.comp (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom
  have hψ : Function.Surjective ψ := by
    intro s
    obtain ⟨y, hy⟩ := hσbar s
    refine ⟨(Subgroup.subgroupOfEquivOfLe hle).symm y, ?_⟩
    simp [ψ, hy]
  exact isCompositionFactor_of_subnormal_surjection hsub hKs ψ hψ

theorem s9c_ringhom_s9P2 {R S : Type} [Ring R] [Ring S] (φ : R →+* S) (M : R) :
    s9P2 (φ M) = φ (s9P2 M) := by
  simp [s9P2, map_add, map_mul, map_one]

theorem s9c_conj_cancel {E : Type} [Field E] {n : ℕ} (P : GL (Fin n) E)
    (A B : Matrix (Fin n) (Fin n) E)
    (h : (P : Matrix (Fin n) (Fin n) E) * A * ((P⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *
      ((P : Matrix (Fin n) (Fin n) E) * B * ((P⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) = 1) :
    A * B = 1 := by
  have h1 : (P : Matrix (Fin n) (Fin n) E) * (A * B) *
      ((P⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = 1 := by
    rw [← h]
    simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv_cancel_left,
      Units.inv_mul, Matrix.mul_one, Matrix.one_mul]
  calc A * B = ((P⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *
        ((P : Matrix (Fin n) (Fin n) E) * (A * B) *
          ((P⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) *
          (P : Matrix (Fin n) (Fin n) E) := by
        simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul,
          Matrix.mul_one, Matrix.one_mul]
    _ = 1 := by
        rw [h1]
        simp only [Matrix.mul_one, Units.inv_mul]

theorem s9c_conj_zero {E : Type} [Field E] {n : ℕ} (P : GL (Fin n) E)
    (Z : Matrix (Fin n) (Fin n) E)
    (h : (P : Matrix (Fin n) (Fin n) E) * Z * ((P⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = 0) :
    Z = 0 := by
  calc Z = ((P⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *
        ((P : Matrix (Fin n) (Fin n) E) * Z * ((P⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) *
          (P : Matrix (Fin n) (Fin n) E) := by
        simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul,
          Matrix.mul_one, Matrix.one_mul]
    _ = 0 := by
        rw [h]
        simp

theorem s9c_two_matrix {E : Type} [Field E] [CharP E 2] (n : ℕ) :
    (2 : Matrix (Fin n) (Fin n) E) = 0 := by
  have h2E : (2 : E) = 0 := by exact_mod_cast CharP.cast_eq_zero E 2
  ext i j
  simp [Matrix.ofNat_apply, h2E]

end CFSG.Quasithin.H13.L829N
