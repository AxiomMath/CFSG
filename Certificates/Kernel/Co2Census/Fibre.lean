module

public import Certificates.Kernel.Co2Census.S0

public section

namespace CertificateChecks.KernelCo2Census

open CFSG.Sporadic.Co2Smith CFSG.KC.Co2InvS CFSG.KC.Co2Census

variable {M : Type*} [Group M] [Finite M]

@[expose] noncomputable def fib (π : M →* K) (P : M → Prop) (s : K) : ℕ :=
  Nat.card {y : M // π y = s ∧ P y}

theorem card_eq_sum_fib (π : M →* K) (P : M → Prop) (T : Finset K) (hT : ∀ y, P y → π y ∈ T) :
    Nat.card {y : M // P y} = ∑ s ∈ T, fib π P s := by
  classical
  have : Fintype M := Fintype.ofFinite M
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_eq_sum_card_fiberwise (f := fun y => π y) (t := T) (fun y hy =>
      hT y (Finset.mem_filter.1 hy).2)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [fib, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_filter]
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_comm

theorem fib_conj (π : M →* K) (P : M → Prop) {u : M} (hu : ∀ y, P (u * y * u⁻¹) ↔ P y) (s : K) :
    fib π P (π u * s * (π u)⁻¹) = fib π P s := by
  unfold fib
  refine (Nat.card_congr
    { toFun := fun y => ⟨u⁻¹ * y.1 * u, ?_, ?_⟩
      invFun := fun y => ⟨u * y.1 * u⁻¹, ?_, ?_⟩
      left_inv := fun y => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc]) })
  · rw [map_mul, map_mul, y.2.1, map_inv]
    group
  · have := (hu (u⁻¹ * y.1 * u)).1
    rw [show u * (u⁻¹ * y.1 * u) * u⁻¹ = y.1 by group] at this
    exact this y.2.2
  · rw [map_mul, map_mul, y.2.1, map_inv]
  · exact (hu y.1).2 y.2.2

@[expose] def invSub (P : M → Prop) : Subgroup M where
  carrier := {u | ∀ y, P (u * y * u⁻¹) ↔ P y}
  mul_mem' := fun {a b} ha hb y => by
    rw [show a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ by group, ha, hb]
  one_mem' := fun y => by simp
  inv_mem' := fun {a} ha y => by
    rw [← ha (a⁻¹ * y * a⁻¹⁻¹), show a * (a⁻¹ * y * a⁻¹⁻¹) * a⁻¹ = y by group]

theorem fib_conj_closure (π : M →* K) (P : M → Prop) {w : ℕ → M} {ngen : ℕ}
    (hw : ∀ l < ngen, ∀ y, P (w l * y * (w l)⁻¹) ↔ P y) {g : K}
    (hg : g ∈ gensSub (fun l => π (w l)) ngen) (s : K) :
    fib π P (g * s * g⁻¹) = fib π P s := by
  have hcl : gensSub (fun l => π (w l)) ngen = (gensSub w ngen).map π := by
    rw [gensSub, gensSub, MonoidHom.map_closure, Set.image_image]
  rw [hcl] at hg
  obtain ⟨u, hu, rfl⟩ := hg
  have hle : gensSub w ngen ≤ invSub P := by
    rw [gensSub, Subgroup.closure_le]
    rintro _ ⟨l, hl, rfl⟩
    exact hw l hl
  exact fib_conj π P (hle hu) s

theorem fib_record (π : M →* K) (P : M → Prop) {w : ℕ → M} {step : ℕ → ℕ → ℕ} {ngen N : ℕ}
    {Pt IX : ℕ → ℕ} (hs : ConjSteps repK step ngen fun l => π (w l))
    (hw : ∀ l < ngen, ∀ y, P (w l * y * (w l)⁻¹) ↔ P y)
    (ht : ∀ i < N, treeK step ngen N Pt IX i = true) {x : ℕ → K}
    (hx : ∀ i < N, repK (x i) (Pt i)) {i : ℕ} (hi : i < N) :
    fib π P (x i) = fib π P (x (rtOf IX i)) := by
  obtain ⟨hrt, -, hreach⟩ := (treeK_sound ht).1 i hi
  obtain ⟨g, hg, hr⟩ := reach_conj hs hreach (hx _ hrt)
  rw [repK_fun (hx i hi) hr]
  exact fib_conj_closure π P hw hg _

theorem sum_range_list (n : ℕ) (f : ℕ → ℕ) :
    ∑ j ∈ Finset.range n, f j = ((List.range n).map f).sum := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append,
      List.map_singleton, List.sum_singleton]

theorem card_query (π : M →* K) (P : M → Prop) {w : ℕ → M} {step : ℕ → ℕ → ℕ} {ngen N nr hi : ℕ}
    {Pt IX RTk : ℕ → ℕ} {xr : ℕ → K} (hs : ConjSteps repK step ngen fun l => π (w l))
    (hw : ∀ l < ngen, ∀ y, P (w l * y * (w l)⁻¹) ↔ P y)
    (ht : ∀ i < N, treeK step ngen N Pt IX i = true)
    (hroots : ∀ i < N, ∃ j < nr, rtOf IX i = RTk j)
    (hdist : ∀ j < nr, ∀ j' < nr, RTk j = RTk j' → j = j')
    (hrk : ∀ j < nr, RTk j < N ∧ rtOf IX (RTk j) = RTk j ∧ repK (xr j) (Pt (RTk j)))
    (hsupp : ∀ y, P y → ∃ i < N, repK (π y) (Pt i)) (hN : N ≤ 64 * hi) :
    Nat.card {y : M // P y} =
      ∑ j ∈ Finset.range nr, rootCount IX N hi (RTk j) * fib π P (xr j) := by
  classical
  have tf := treeK_sound ht
  have hex : ∀ i < N, ∃ x, repK x (Pt i) := by
    intro i hi'
    obtain ⟨-, -, hreach⟩ := tf.1 i hi'
    obtain ⟨j, hj, hji⟩ := hroots i hi'
    rw [hji] at hreach
    obtain ⟨g, -, hg⟩ := reach_conj hs hreach (hrk j hj).2.2
    exact ⟨_, hg⟩
  let x : ℕ → K := fun i => if h : ∃ x, repK x (Pt i) then h.choose else 1
  have hx : ∀ i < N, repK (x i) (Pt i) := by
    intro i hi'
    simp only [x, dif_pos (hex i hi')]
    exact (hex i hi').choose_spec
  have hxinj : Set.InjOn x (Finset.range N : Set ℕ) := by
    intro i hi' j hj e
    rw [Finset.coe_range, Set.mem_Iio] at hi' hj
    have h1 := hx i hi'
    rw [show x i = x j from e] at h1
    exact tf.2 i hi' j hj (repK_unique h1 (hx j hj))
  rw [card_eq_sum_fib π P ((Finset.range N).image x) (fun y hy => by
    obtain ⟨i, hi', hr⟩ := hsupp y hy
    exact Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi', repK_fun (hx i hi') hr⟩),
    Finset.sum_image hxinj]
  have hroot : ∀ i ∈ Finset.range N, fib π P (x i) = fib π P (x (rtOf IX i)) := fun i hi' =>
    fib_record π P hs hw ht hx (Finset.mem_range.1 hi')
  rw [Finset.sum_congr rfl hroot]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun i => rtOf IX i) (t := (Finset.range nr).image RTk)
    (fun i hi' => by
      obtain ⟨j, hj, e⟩ := hroots i (Finset.mem_range.1 hi')
      exact Finset.mem_image.2 ⟨j, Finset.mem_range.2 hj, e.symm⟩)]
  rw [Finset.sum_image (fun j hj j' hj' e => hdist j (Finset.mem_range.1 hj) j'
    (Finset.mem_range.1 hj') e)]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  obtain ⟨hk, hkk, hrep⟩ := hrk j hj'
  rw [Finset.sum_congr rfl (fun i hi' => by rw [(Finset.mem_filter.1 hi').2]),
    Finset.sum_const, smul_eq_mul, rootCount_eq hN, repK_fun (hx _ hk) hrep]

theorem fib_elt
    {elt : ℕ → ℕ → M} {π : M →* K}
    (hsurj : ∀ y, ∃ e < 512, ∃ n < 1451520, elt e n = y)
    (hinj : ∀ e e' n n', e < 512 → e' < 512 → n < 1451520 → n' < 1451520 → elt e n = elt e' n' →
      e = e' ∧ n = n')
    (hpi : ∀ e n, π (elt e n) = sElt n) (P : M → Prop) [DecidablePred P] {n : ℕ}
    (hn : n < 1451520) :
    fib π P (sElt n) = ((Finset.range 512).filter fun e => P (elt e n)).card := by
  classical
  unfold fib
  rw [← Nat.card_eq_finsetCard]
  have key : ∀ y : M, π y = sElt n → ∃ e < 512, elt e n = y := by
    intro y hy
    obtain ⟨e, he, n', hn', rfl⟩ := hsurj y
    rw [hpi] at hy
    obtain rfl := sElt_injOn hn' hn hy
    exact ⟨e, he, rfl⟩
  refine Nat.card_congr
    { toFun := fun y => ⟨Classical.choose (key y.1 y.2.1), Finset.mem_filter.2
        ⟨Finset.mem_range.2 (Classical.choose_spec (key y.1 y.2.1)).1, by
          rw [(Classical.choose_spec (key y.1 y.2.1)).2]
          exact y.2.2⟩⟩
      invFun := fun e => ⟨elt e.1 n, hpi _ _, (Finset.mem_filter.1 e.2).2⟩
      left_inv := fun y => Subtype.ext (Classical.choose_spec (key y.1 y.2.1)).2
      right_inv := fun e => Subtype.ext ?_ }
  have h1 := Classical.choose_spec (key (elt e.1 n) (hpi _ _))
  exact (hinj _ _ _ _ h1.1 (Finset.mem_range.1 (Finset.mem_filter.1 e.2).1) hn hn h1.2).1

end CertificateChecks.KernelCo2Census

end
