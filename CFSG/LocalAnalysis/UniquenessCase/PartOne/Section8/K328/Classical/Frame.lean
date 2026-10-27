module

public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.CharP.Reduced
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

private theorem k328frame_symm {F V : Type} [Field F] [CharP F 2] [AddCommGroup V] [Module F V]
    (B : LinearMap.BilinForm F V) (halt : ∀ x, B x x = 0) (x y : V) : B x y = B y x :=
  (CharTwo.neg_eq (B x y)).symm.trans ((show B.IsAlt from halt).neg_eq x y)

private theorem k328frame_add_self_eq_zero {F V : Type} [Ring F] [CharP F 2] [AddCommGroup V]
    [Module F V] (x : V) : x + x = 0 := by
  have h : (1 : F) • x + (1 : F) • x = 0 := by
    rw [← add_smul, CharTwo.add_self_eq_zero, zero_smul]
  simpa using h

private theorem k328frame_neg_eq {F V : Type} [Ring F] [CharP F 2] [AddCommGroup V]
    [Module F V] (x : V) : -x = x := by
  rw [← neg_one_smul F x, CharTwo.neg_eq (1 : F), one_smul]

private theorem k328frame_eq_of_add_eq_zero {F V : Type} [Ring F] [CharP F 2] [AddCommGroup V]
    [Module F V] {a b : V} (h : a + b = 0) : a = b := by
  have h1 : -a = b := neg_eq_of_add_eq_zero_right h
  rw [k328frame_neg_eq (F := F) a] at h1
  exact h1

private theorem k328frame_zz {F V : Type} [Field F] [CharP F 2] [AddCommGroup V] [Module F V]
    (z : V →ₗ[F] V) (hz3 : ∀ x, z (z x) + z x + x = 0) (x : V) : z (z x) = z x + x := by
  have h : z (z x) + (z x + x) = 0 := by rw [← add_assoc]; exact hz3 x
  exact k328frame_eq_of_add_eq_zero (F := F) h

private theorem k328frame_linearIndependent_sum_elim
    {F V ι : Type} [Field F] [AddCommGroup V] [Module F V] [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm F V) (hsym : ∀ x y, B x y = B y x)
    (f g : ι → V)
    (hfg : ∀ i j, B (f i) (g j) = if i = j then 1 else 0)
    (hff : ∀ i j, B (f i) (f j) = 0)
    (hgg : ∀ i j, B (g i) (g j) = 0) :
    LinearIndependent F (Sum.elim f g) := by
  let φ : V →ₗ[F] (ι ⊕ ι → F) :=
    LinearMap.pi (Sum.elim (fun j => B.flip (g j)) (fun j => B.flip (f j)))
  have hcomp : φ ∘ Sum.elim f g = fun p : ι ⊕ ι => Pi.single p (1 : F) := by
    funext p
    rcases p with i | i <;> funext q <;> rcases q with j | j
    · simp only [φ, Function.comp_apply, LinearMap.pi_apply, Sum.elim_inl]
      rw [LinearMap.BilinForm.flip_apply, hfg i j, Pi.single_apply]
      simp [Sum.inl.injEq, eq_comm]
    · simp only [φ, Function.comp_apply, LinearMap.pi_apply, Sum.elim_inl, Sum.elim_inr]
      rw [LinearMap.BilinForm.flip_apply, hff i j, Pi.single_apply]
      simp
    · simp only [φ, Function.comp_apply, LinearMap.pi_apply, Sum.elim_inl, Sum.elim_inr]
      rw [LinearMap.BilinForm.flip_apply, hgg i j, Pi.single_apply]
      simp
    · simp only [φ, Function.comp_apply, LinearMap.pi_apply, Sum.elim_inr]
      rw [LinearMap.BilinForm.flip_apply, hsym (g i) (f j), hfg j i, Pi.single_apply]
      simp [Sum.inr.injEq, eq_comm]
  have hli : LinearIndependent F (φ ∘ Sum.elim f g) := by
    rw [hcomp]
    exact Pi.linearIndependent_single_one (ι ⊕ ι) F
  exact LinearIndependent.of_comp φ hli


private theorem k328frame_aux (F : Type) [Field F] [Finite F] [CharP F 2] :
    ∀ (n : ℕ), ∀ {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V],
      Module.finrank F V = n →
      ∀ (B : LinearMap.BilinForm F V), (∀ x, (∀ y, B x y = 0) → x = 0) →
      (∀ x, B x x = 0) →
      ∀ (z : V →ₗ[F] V), (∀ x y, B (z x) (z y) = B x y) →
      (∀ x, z (z x) + z x + x = 0) →
      ∃ (k : ℕ) (v : Fin k → V), 2 * k = Module.finrank F V ∧
        LinearIndependent F (Sum.elim v (fun i => z (v i))) ∧
        (∀ i j, B (v i) (z (v j)) = if i = j then 1 else 0) ∧
        (∀ i j, B (v i) (v j) = 0) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ _ _ hdim B hB halt z hz hz3
    by_cases hex : ∃ v : V, B v (z v) ≠ 0
    · obtain ⟨v₀, hv₀⟩ := hex
      have hsym : ∀ x y : V, B x y = B y x := k328frame_symm B halt
      obtain ⟨c, hc⟩ := isSquare_of_charTwo' (B v₀ (z v₀))⁻¹
      let v : V := c • v₀
      have hv : B v (z v) = 1 := by
        have : B v (z v) = (c * c) * B v₀ (z v₀) := by
          simp only [v, map_smul, LinearMap.smul_apply, smul_eq_mul]
          ring
        rw [this, ← hc, inv_mul_cancel₀ hv₀]
      let P : Submodule F V := Submodule.span F ({v, z v} : Set V)
      have hvP : v ∈ P := Submodule.subset_span (by simp)
      have hzvP : z v ∈ P := Submodule.subset_span (by simp)
      have hzP : ∀ x ∈ P, z x ∈ P := by
        have hmap : Submodule.map z P ≤ P := by
          dsimp only [P]
          rw [Submodule.map_span]
          refine Submodule.span_le.mpr ?_
          rintro y ⟨x, hx, rfl⟩
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl
          · exact hzvP
          · rw [k328frame_zz z hz3 v]
            exact P.add_mem hzvP hvP
        intro x hx
        exact hmap (Submodule.mem_map.mpr ⟨x, hx, rfl⟩)
      let Q : Submodule F V := B.orthogonal P
      have hQv : ∀ x ∈ Q, B v x = 0 := fun x hx => hx v hvP
      have hQzv : ∀ x ∈ Q, B (z v) x = 0 := fun x hx => hx (z v) hzvP
      have hzQ : ∀ x ∈ Q, z x ∈ Q := by
        intro x hx
        refine (LinearMap.BilinForm.mem_orthogonal_iff).mpr ?_
        intro p hp
        have h1 : B (z p) (z x) = 0 := by rw [hz p x]; exact hx p hp
        have h2 : B (z p + p) (z x) = 0 := by
          rw [← k328frame_zz z hz3 p]
          rw [hz (z p) x]
          exact hx (z p) (hzP p hp)
        have h3 : B (z p) (z x) + B p (z x) = 0 := by
          rw [← LinearMap.add_apply, ← map_add]
          exact h2
        rw [h1, zero_add] at h3
        exact h3
      let zQ : Q →ₗ[F] Q := z.restrict hzQ
      let BQ : LinearMap.BilinForm F Q := B.restrict Q
      have hBQ_apply : ∀ x y : Q, BQ x y = B (x : V) (y : V) := fun x y => rfl
      have hli2 : LinearIndependent F (![v, z v] : Fin 2 → V) := by
        rw [LinearIndependent.pair_iff]
        intro s t hst
        have h1 : B (s • v + t • (z v)) (z v) = s := by
          simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hv, halt, smul_eq_mul,
            mul_one, mul_zero, add_zero]
        have h2 : B (s • v + t • (z v)) v = t := by
          have hsym_zv : B (z v) v = 1 := by rw [hsym (z v) v, hv]
          simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, halt, hsym_zv, smul_eq_mul,
            mul_one, mul_zero, zero_add]
        constructor
        · have h := h1
          rw [hst] at h
          simp only [map_zero, LinearMap.zero_apply] at h
          exact h.symm
        · have h := h2
          rw [hst] at h
          simp only [map_zero, LinearMap.zero_apply] at h
          exact h.symm
      have hPnd : (B.restrict P).Nondegenerate := by
        constructor
        · intro x hx
          obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp x.2
          have hxzv : B (x : V) (z v) = 0 := by simpa using hx ⟨z v, hzvP⟩
          have hxv : B (x : V) v = 0 := by simpa using hx ⟨v, hvP⟩
          have ha : a = 0 := by
            have h : B (x : V) (z v) = a := by
              rw [← hab]
              simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hv, halt, smul_eq_mul,
                mul_one, mul_zero, add_zero]
            rw [h] at hxzv; exact hxzv
          have hb : b = 0 := by
            have hsym_zv : B (z v) v = 1 := by rw [hsym (z v) v, hv]
            have h : B (x : V) v = b := by
              rw [← hab]
              simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, halt, hsym_zv,
                smul_eq_mul, mul_one, mul_zero, zero_add]
            rw [h] at hxv; exact hxv
          apply Subtype.ext
          rw [← hab, ha, hb, zero_smul, zero_smul, add_zero, Submodule.coe_zero]
        · intro x hx
          obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp x.2
          have hxzv : B (z v) (x : V) = 0 := by simpa using hx ⟨z v, hzvP⟩
          have hxv : B v (x : V) = 0 := by simpa using hx ⟨v, hvP⟩
          have hzvzv : B (z v) (z v) = 0 := by rw [hz v v, halt]
          have ha : a = 0 := by
            have h : B (z v) (x : V) = a := by
              rw [← hab]
              simp only [map_add, map_smul, hsym (z v) v, hv,
                hzvzv, smul_eq_mul, mul_one, mul_zero, add_zero]
            rw [h] at hxzv; exact hxzv
          have hb : b = 0 := by
            have h : B v (x : V) = b := by
              rw [← hab]
              simp only [map_add, map_smul, halt, hv, smul_eq_mul,
                mul_one, mul_zero, zero_add]
            rw [h] at hxv; exact hxv
          apply Subtype.ext
          rw [← hab, ha, hb, zero_smul, zero_smul, add_zero, Submodule.coe_zero]
      have hrefl : B.IsRefl := fun x y h => by rwa [hsym x y] at h
      have hBnd : B.Nondegenerate :=
        ⟨hB, fun y hy => hB y (fun x => by rw [hsym y x]; exact hy x)⟩
      have hcompl : IsCompl P Q := by
        have h := LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
          (B := B) (W := P) hrefl hPnd
        simpa only [Q] using h
      have hQnd : (B.restrict Q).Nondegenerate := by
        refine LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal
          (B := B) (W := Q) hrefl ?_
        have horth : B.orthogonal Q = P := by
          show B.orthogonal (B.orthogonal P) = P
          exact LinearMap.BilinForm.orthogonal_orthogonal (B := B) hBnd hrefl P
        rw [horth]
        exact hcompl.disjoint.symm
      have hfinP : Module.finrank F P = 2 := by
        have hv_ne : v ≠ z v := by
          intro h
          rw [← h] at hv
          rw [halt] at hv
          exact one_ne_zero hv.symm
        have hspan_le : P ≤ Submodule.span F (Set.range (![v, z v] : Fin 2 → V)) := by
          dsimp only [P]
          refine Submodule.span_le.mpr ?_
          rintro x (rfl | rfl)
          · exact Submodule.subset_span ⟨0, rfl⟩
          · exact Submodule.subset_span ⟨1, rfl⟩
        have hspan_ge : Submodule.span F (Set.range (![v, z v] : Fin 2 → V)) ≤ P := by
          refine Submodule.span_le.mpr ?_
          rintro x ⟨i, rfl⟩
          fin_cases i <;> exact Submodule.subset_span (by simp)
        have h1 : Module.finrank F (Submodule.span F (Set.range (![v, z v] : Fin 2 → V))) = 2 := by
          rw [finrank_span_eq_card hli2]; simp
        have hle : Module.finrank F P ≤ 2 := by
          calc Module.finrank F P
              ≤ Module.finrank F (Submodule.span F (Set.range (![v, z v] : Fin 2 → V))) :=
                Submodule.finrank_mono hspan_le
            _ = 2 := h1
        have hge : 2 ≤ Module.finrank F P := by
          calc 2 = Module.finrank F (Submodule.span F (Set.range (![v, z v] : Fin 2 → V))) :=
                h1.symm
            _ ≤ Module.finrank F P := Submodule.finrank_mono hspan_ge
        omega
      have hdimQ : Module.finrank F Q = n - 2 := by
        have h := LinearMap.BilinForm.finrank_orthogonal (B := B) hBnd P
        dsimp only [Q]
        rw [hfinP, hdim] at h
        exact h
      have h2n : 2 ≤ n := by
        have hle := Submodule.finrank_le (R := F) P
        rw [hfinP, hdim] at hle
        exact hle
      obtain ⟨k, w, hk2, _hwLI, hwB, hwBB⟩ :=
        ih (Module.finrank F Q) (by rw [hdimQ]; omega) (V := Q) rfl BQ hQnd.1
          (fun x => by
            change B (x : V) (x : V) = 0
            exact halt (x : V))
          zQ
          (fun x y => by
            change B (zQ x : V) (zQ y : V) = B (x : V) (y : V)
            simp only [zQ, LinearMap.coe_restrict_apply]
            exact hz (x : V) (y : V))
          (fun x => by
            apply Subtype.ext
            change z (zQ x : V) + zQ x + (x : V) = 0
            simp only [zQ, LinearMap.coe_restrict_apply]
            exact hz3 (x : V))
      let vNew : Fin (k + 1) → V := Fin.cons v (fun i => (w i : V))
      have hfgNew : ∀ i j, B (vNew i) (z (vNew j)) = if i = j then 1 else 0 := by
        intro i j
        revert j
        refine Fin.cases ?_ ?_ i
        · intro j
          refine Fin.cases ?_ ?_ j
          · simpa [vNew, Fin.cons_zero] using hv
          · intro j
            have h0 : B v (z (w j : V)) = 0 := hQv (z (w j : V)) (hzQ (w j) (w j).2)
            simp only [vNew, Fin.cons_zero, Fin.cons_succ]
            rw [if_neg (Fin.succ_ne_zero j).symm]
            exact h0
        · intro i j
          refine Fin.cases ?_ ?_ j
          · have h0 : B (w i : V) (z v) = 0 := by
              rw [hsym (w i : V) (z v)]
              exact hQzv (w i) (w i).2
            simp only [vNew, Fin.cons_zero, Fin.cons_succ]
            rw [if_neg (Fin.succ_ne_zero i)]
            exact h0
          · intro j
            have h0 : B (w i : V) (z (w j : V)) = if i = j then 1 else 0 := by
              have hh := hwB i j
              rw [hBQ_apply] at hh
              simpa only [zQ, LinearMap.coe_restrict_apply] using hh
            simp only [vNew, Fin.cons_succ, Fin.succ_inj]
            exact h0
      have hffNew : ∀ i j, B (vNew i) (vNew j) = 0 := by
        intro i j
        revert j
        refine Fin.cases ?_ ?_ i
        · intro j
          refine Fin.cases ?_ ?_ j
          · simpa [vNew, Fin.cons_zero] using halt v
          · intro j
            simp only [vNew, Fin.cons_zero, Fin.cons_succ]
            exact hQv (w j) (w j).2
        · intro i j
          refine Fin.cases ?_ ?_ j
          · have h0 : B (w i : V) v = 0 := by
              rw [hsym (w i : V) v]
              exact hQv (w i) (w i).2
            simpa only [vNew, Fin.cons_zero, Fin.cons_succ] using h0
          · intro j
            have h0 : B (w i : V) (w j : V) = 0 := by
              have hh := hwBB i j
              rw [hBQ_apply] at hh
              exact hh
            simpa only [vNew, Fin.cons_succ] using h0
      have hggNew : ∀ i j, B (z (vNew i)) (z (vNew j)) = 0 := by
        intro i j
        revert j
        refine Fin.cases ?_ ?_ i
        · intro j
          refine Fin.cases ?_ ?_ j
          · simp only [vNew, Fin.cons_zero]
            rw [hz v v, halt]
          · intro j
            have h0 : B v (w j : V) = 0 := hQv (w j) (w j).2
            simp only [vNew, Fin.cons_zero, Fin.cons_succ]
            rw [hz v (w j : V)]
            exact h0
        · intro i j
          refine Fin.cases ?_ ?_ j
          · have h0 : B (w i : V) v = 0 := by
              rw [hsym (w i : V) v]
              exact hQv (w i) (w i).2
            simp only [vNew, Fin.cons_zero, Fin.cons_succ]
            rw [hz (w i : V) v]
            exact h0
          · intro j
            have h0 : B (w i : V) (w j : V) = 0 := by
              have hh := hwBB i j
              rw [hBQ_apply] at hh
              exact hh
            simp only [vNew, Fin.cons_succ]
            rw [hz (w i : V) (w j : V)]
            exact h0
      refine ⟨k + 1, vNew, ?_, ?_, hfgNew, hffNew⟩
      · have hk2' : 2 * k = n - 2 := by rw [← hdimQ]; exact hk2
        rw [hdim]
        omega
      · exact k328frame_linearIndependent_sum_elim B hsym vNew (fun i => z (vNew i))
          hfgNew hffNew hggNew
    · simp only [not_exists, not_not] at hex
      have hzero : ∀ x : V, x = 0 := by
        intro x
        apply hB x
        intro w
        have hI : B w (z x) + B x (z w) = 0 := by
          simpa only [map_add, LinearMap.add_apply, hex x, hex w, zero_add, add_zero]
            using hex (x + w)
        have hII : B w (z x) = B w x + B (z w) x := by
          calc B w (z x) = B (z w) (z (z x)) := (hz w (z x)).symm
            _ = B (z w) (z x + x) := by rw [k328frame_zz z hz3 x]
            _ = B (z w) (z x) + B (z w) x := by rw [map_add]
            _ = B w x + B (z w) x := by rw [hz w x]
        have hwx : B w x = 0 := by
          have h2 : (B w x + B x (z w)) + B x (z w) = 0 := by
            rw [hII] at hI
            rwa [k328frame_symm B halt (z w) x] at hI
          have h3 : (B w x + B x (z w)) + B x (z w) = B w x := by
            rw [show (B w x + B x (z w)) + B x (z w) =
              B w x + (B x (z w) + B x (z w)) by abel,
              k328frame_add_self_eq_zero (F := F), add_zero]
          rw [h3] at h2
          exact h2
        rw [k328frame_symm B halt x w]
        exact hwx
      have hfin : Module.finrank F V = 0 := finrank_zero_iff_forall_zero.mpr hzero
      refine ⟨0, Fin.elim0, ?_, linearIndependent_empty_type, ?_, ?_⟩
      · rw [hfin]
      · intro i; exact Fin.elim0 i
      · intro i; exact Fin.elim0 i


theorem k328_isometry_frame {F V : Type} [Field F] [Finite F] [CharP F 2] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (B : LinearMap.BilinForm F V)
    (hB : ∀ x, (∀ y, B x y = 0) → x = 0) (halt : ∀ x, B x x = 0)
    (z : V →ₗ[F] V) (hz : ∀ x y, B (z x) (z y) = B x y) (hz3 : ∀ x, z (z x) + z x + x = 0) :
    ∃ (k : ℕ) (v : Fin k → V), 2 * k = Module.finrank F V ∧
      LinearIndependent F (Sum.elim v (fun i => z (v i))) ∧
      (∀ i j, B (v i) (z (v j)) = if i = j then 1 else 0) ∧ (∀ i j, B (v i) (v j) = 0) := by
  exact k328frame_aux F (Module.finrank F V) (V := V) rfl B hB halt z hz hz3

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
