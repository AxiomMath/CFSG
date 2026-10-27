module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeOrthSpOne

public section

namespace CFSG.StandardType.TwoThreeOrth

open Matrix Module CFSG.Assembly CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.SeitzReduction.SymplecticPilot
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)

variable {K : Type} [Field K] {k : ℕ}

section Supp

variable {n : ℕ}

theorem isSupp_mono {S T : Set (Fin n ⊕ Fin n)} (hST : S ⊆ T)
    {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K} (h : IsSupp S M) : IsSupp T M :=
  fun r t hrt => h r t fun h' => hrt ⟨hST h'.1, hST h'.2⟩

theorem isSupp_inter_iff {A B : Set (Fin n ⊕ Fin n)}
    {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K} :
    IsSupp (A ∩ B) M ↔ IsSupp A M ∧ IsSupp B M := by
  constructor
  · intro h
    exact ⟨isSupp_mono Set.inter_subset_left h, isSupp_mono Set.inter_subset_right h⟩
  · rintro ⟨hA, hB⟩ r t hrt
    by_cases h : r ∈ A ∧ t ∈ A
    · exact hB r t fun h' => hrt ⟨⟨h.1, h'.1⟩, ⟨h.2, h'.2⟩⟩
    · exact hA r t h

theorem eq_smul_add_smul_of_supp {j : Fin n} {v : Fin n ⊕ Fin n → K}
    (hv : ∀ r ∉ coords j, v r = 0) :
    v = v (Sum.inl j) • Pi.single (Sum.inl j) 1 + v (Sum.inr j) • Pi.single (Sum.inr j) 1 := by
  funext r
  by_cases h1 : r = Sum.inl j
  · subst h1
    simp
  · by_cases h2 : r = Sum.inr j
    · subst h2
      simp
    · rw [hv r (fun h => by rcases mem_coords.1 h with rfl | rfl <;> contradiction)]
      simp [h1, h2]

theorem form_plane (j : Fin n) (α β γ δ : K) :
    form (α • Pi.single (Sum.inl j) 1 + β • Pi.single (Sum.inr j) 1)
      (γ • Pi.single (Sum.inl j) 1 + δ • Pi.single (Sum.inr j) 1) = α * δ - β * γ := by
  have hef := form_single_inl_inr (K := K) j
  have hfe : form (Pi.single (Sum.inr j) (1 : K) : Fin n ⊕ Fin n → K)
      (Pi.single (Sum.inl j) 1) = -1 := by rw [form_antisymm, hef]
  simp only [form_add_left, form_add_right, form_smul_left, form_smul_right, form_self, hef,
    hfe]
  ring

end Supp

section Planes

theorem zero_ne_one_fin : (0 : Fin (k + 2)) ≠ 1 := by simp

theorem parClosed_coords_union : ParClosed (coords (0 : Fin (k + 2)) ∪ coords 1) := by
  rintro a (h | h)
  · exact Or.inl (parClosed_coords 0 a h)
  · exact Or.inr (parClosed_coords 1 a h)

theorem nsElt_mem_suppGroup_union {j : Fin (k + 2)} (hj : j = 0 ∨ j = 1) :
    nsElt (K := K) j ∈ suppGroup (coords (0 : Fin (k + 2)) ∪ coords 1) := by
  refine isSupp_mono ?_ (isSupp_longBlock (K := K) j zThreeSL)
  rcases hj with rfl | rfl
  · exact Set.subset_union_left
  · exact Set.subset_union_right

theorem commute_nsElt_zero_one : Commute (nsElt (K := K) (n := k + 2) 0) (nsElt 1) := by
  have h := nsElt_mem_complSp (K := K) (k := (0 : Fin (k + 2))) (l := 1) zero_ne_one_fin.symm
  rw [Commute, SemiconjBy]
  exact Subgroup.mem_centralizer_iff.mp (complSp_le_centralizer_nsTorusSp 0 h) _
    (nsElt_mem_nsTorusSp 0)

theorem exists_succ_succ_eq {i : Fin (k + 2)} (h0 : i ≠ 0) (h1 : i ≠ 1) :
    ∃ j : Fin k, j.succ.succ = i := by
  obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.mpr h0
  have : i' ≠ 0 := fun h => h1 (by rw [h]; rfl)
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr this
  exact ⟨j, rfl⟩

theorem succ_succ_ne_one (j : Fin k) : j.succ.succ ≠ (1 : Fin (k + 2)) := by
  intro h
  rw [← Fin.succ_zero_eq_one] at h
  exact Fin.succ_ne_zero j (Fin.succ_injective _ h)

theorem succ_succ_injective : Function.Injective (fun j : Fin k => j.succ.succ) :=
  fun _ _ h => Fin.succ_injective _ (Fin.succ_injective _ h)

theorem range_spEmbed_succ_succ :
    (spEmbed (K := K) (fun j : Fin k => j.succ.succ) succ_succ_injective).range =
      complSp K (0 : Fin (k + 2)) ⊓ complSp K 1 := by
  rw [range_spEmbed]
  have hset : Set.range (Sum.map (fun j : Fin k => j.succ.succ) (fun j : Fin k => j.succ.succ)) =
      (coords (0 : Fin (k + 2)))ᶜ ∩ (coords 1)ᶜ := by
    ext a
    simp only [Set.mem_range, Set.mem_inter_iff, Set.mem_compl_iff, mem_coords]
    constructor
    · rintro ⟨b, rfl⟩
      rcases b with j | j <;> simp [Fin.succ_ne_zero, succ_succ_ne_one]
    · intro ha
      rcases a with i | i
      · obtain ⟨j, rfl⟩ := exists_succ_succ_eq (k := k) (i := i) (by simpa using ha.1)
          (by simpa using ha.2)
        exact ⟨Sum.inl j, rfl⟩
      · obtain ⟨j, rfl⟩ := exists_succ_succ_eq (k := k) (i := i) (by simpa using ha.1)
          (by simpa using ha.2)
        exact ⟨Sum.inr j, rfl⟩
  ext x
  rw [Subgroup.mem_inf, complSp, complSp, mem_suppGroup, mem_suppGroup, mem_suppGroup, hset,
    isSupp_inter_iff]

theorem nonempty_mulEquiv_inf_complSp :
    Nonempty (StatedSp k K ≃* ↥(complSp K (0 : Fin (k + 2)) ⊓ complSp K 1)) :=
  ⟨(MonoidHom.ofInjective (spEmbed_injective (K := K) succ_succ_injective)).trans
    (MulEquiv.subgroupCongr range_spEmbed_succ_succ)⟩

theorem inf_complSp_le_suppGroup :
    complSp K (0 : Fin (k + 2)) ⊓ complSp K 1 ≤
      suppGroup (coords (0 : Fin (k + 2)) ∪ coords 1)ᶜ := by
  intro x hx
  rw [Set.compl_union]
  exact isSupp_inter_iff.mpr ⟨hx.1, hx.2⟩

end Planes

section Action

theorem inl_not_mem_coords {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    (Sum.inl i : Fin n ⊕ Fin n) ∉ coords j := by
  rw [mem_coords]
  simp [h]

theorem inr_not_mem_coords {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    (Sum.inr i : Fin n ⊕ Fin n) ∉ coords j := by
  rw [mem_coords]
  simp [h]

theorem eq_of_mulVec_single {n : ℕ} {g h : StatedSp n K}
    (hgh : ∀ t, mat n K g *ᵥ Pi.single t 1 = mat n K h *ᵥ Pi.single t 1) : g = h := by
  apply mat_injective
  ext r t
  have := congrFun (hgh t) r
  rwa [mulVec_single_one, mulVec_single_one] at this

theorem mulVec_nsElt_zero_mul_one_of_supp {j : Fin (k + 2)} (hj : j = 0 ∨ j = 1)
    {v : Fin (k + 2) ⊕ Fin (k + 2) → K} (hv : ∀ r ∉ coords j, v r = 0) :
    mat (k + 2) K (nsElt 0 * nsElt 1) *ᵥ v = mat (k + 2) K (nsElt j) *ᵥ v := by
  rw [map_mul, ← mulVec_mulVec]
  rcases hj with rfl | rfl
  · rw [mat_nsElt_mulVec_of_eq_zero 1 (hv _ (inl_not_mem_coords zero_ne_one_fin.symm))
      (hv _ (inr_not_mem_coords zero_ne_one_fin.symm))]
  · rw [mat_nsElt_mulVec_of_eq_zero 0
      (by rw [mulVec_apply_of_isSupp (M := mat (k + 2) K (nsElt 1))
          (isSupp_longBlock (K := K) 1 zThreeSL) v (inl_not_mem_coords zero_ne_one_fin),
        hv _ (inl_not_mem_coords zero_ne_one_fin)])
      (by rw [mulVec_apply_of_isSupp (M := mat (k + 2) K (nsElt 1))
          (isSupp_longBlock (K := K) 1 zThreeSL) v (inr_not_mem_coords zero_ne_one_fin),
        hv _ (inr_not_mem_coords zero_ne_one_fin)])]

theorem single_supp {n : ℕ} {b : Fin n ⊕ Fin n} {j : Fin n} (hb : b ∈ coords j) :
    ∀ r ∉ coords j, (Pi.single b (1 : K) : Fin n ⊕ Fin n → K) r = 0 := fun r hr =>
  Pi.single_eq_of_ne (fun h : r = b => hr (by rw [h]; exact hb)) 1

theorem single_apply_of_not_mem {n : ℕ} {b r : Fin n ⊕ Fin n} {j : Fin n} (hb : b ∉ coords j)
    (hr : r ∈ coords j) : (Pi.single b (1 : K) : Fin n ⊕ Fin n → K) r = 0 :=
  Pi.single_eq_of_ne (fun h : r = b => hb (by rw [← h]; exact hr)) 1

theorem nsElt_zero_mul_one_mem_suppGroup :
    nsElt (K := K) 0 * nsElt 1 ∈ suppGroup (coords (0 : Fin (k + 2)) ∪ coords 1) :=
  mul_mem (nsElt_mem_suppGroup_union (Or.inl rfl)) (nsElt_mem_suppGroup_union (Or.inr rfl))

variable [CharP K 2]

theorem mulVec_nsElt_zero_mul_one_inl {j : Fin (k + 2)} (hj : j = 0 ∨ j = 1) :
    mat (k + 2) K (nsElt 0 * nsElt 1) *ᵥ Pi.single (Sum.inl j) 1 = Pi.single (Sum.inr j) 1 := by
  rw [mulVec_nsElt_zero_mul_one_of_supp hj (single_supp (inl_mem_coords j)),
    mat_nsElt_mulVec_inl]

theorem mulVec_nsElt_zero_mul_one_inr {j : Fin (k + 2)} (hj : j = 0 ∨ j = 1) :
    mat (k + 2) K (nsElt 0 * nsElt 1) *ᵥ Pi.single (Sum.inr j) 1 =
      Pi.single (Sum.inl j) 1 + Pi.single (Sum.inr j) 1 := by
  rw [mulVec_nsElt_zero_mul_one_of_supp hj (single_supp (inr_mem_coords j)),
    mat_nsElt_mulVec_inr]

end Action

section Dichotomy

variable [CharP K 2]

theorem mul_nsElt_zero_eq_of_supp {j : Fin (k + 2)} (hj : j = 0 ∨ j = 1)
    {s : StatedSp (k + 2) K} (hs : s * (nsElt 0 * nsElt 1) = nsElt 0 * nsElt 1 * s)
    (hv : ∀ r ∉ coords j, (mat (k + 2) K s *ᵥ Pi.single (Sum.inl 0) 1) r = 0) :
    s * nsElt 0 = nsElt j * s := by
  have hsg : ∀ x, mat (k + 2) K s *ᵥ (mat (k + 2) K (nsElt 0 * nsElt 1) *ᵥ x) =
      mat (k + 2) K (nsElt 0 * nsElt 1) *ᵥ (mat (k + 2) K s *ᵥ x) := fun x => by
    rw [mulVec_mulVec, ← map_mul, hs, map_mul, ← mulVec_mulVec]
  obtain ⟨v, hvdef⟩ : ∃ v, v = mat (k + 2) K s *ᵥ Pi.single (Sum.inl 0) 1 := ⟨_, rfl⟩
  obtain ⟨u, hudef⟩ : ∃ u, u = mat (k + 2) K s *ᵥ Pi.single (Sum.inr 0) 1 := ⟨_, rfl⟩
  rw [← hvdef] at hv
  have hu : u = mat (k + 2) K (nsElt j) *ᵥ v := by
    rw [hudef, ← mulVec_nsElt_zero_mul_one_inl (K := K) (k := k) (Or.inl rfl), hsg, ← hvdef,
      mulVec_nsElt_zero_mul_one_of_supp hj hv]
  have hus : ∀ r ∉ coords j, u r = 0 := fun r hr => by
    rw [hu, mulVec_apply_of_isSupp (M := mat (k + 2) K (nsElt j))
      (isSupp_longBlock (K := K) j zThreeSL) _ hr, hv r hr]
  have hNu : mat (k + 2) K (nsElt j) *ᵥ u = v + u := by
    rw [← mulVec_nsElt_zero_mul_one_of_supp hj hus, hudef, ← hsg,
      mulVec_nsElt_zero_mul_one_inr (Or.inl rfl), mulVec_add, ← hvdef, ← hudef]
  obtain ⟨α, hα⟩ : ∃ α, α = v (Sum.inl j) := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, β = v (Sum.inr j) := ⟨_, rfl⟩
  have hvd : v = α • Pi.single (Sum.inl j) 1 + β • Pi.single (Sum.inr j) 1 := by
    rw [hα, hβ]
    exact eq_smul_add_smul_of_supp hv
  have hud : u = β • Pi.single (Sum.inl j) 1 + (α + β) • Pi.single (Sum.inr j) 1 := by
    rw [hu, hvd, mulVec_add, mulVec_smul, mulVec_smul, mat_nsElt_mulVec_inl, mat_nsElt_mulVec_inr]
    funext r
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hq : α * (α + β) - β * β = 1 := by
    have h := form_mulVec s (Pi.single (Sum.inl 0) 1) (Pi.single (Sum.inr 0) 1)
    rw [form_single_inl_inr, ← hvdef, ← hudef, hvd, hud, form_plane] at h
    exact h
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  apply eq_of_mulVec_single
  intro t
  rw [map_mul, map_mul, ← mulVec_mulVec, ← mulVec_mulVec]
  by_cases ht : t ∈ coords 0
  · rcases mem_coords.1 ht with rfl | rfl
    · rw [mat_nsElt_mulVec_inl, ← hudef, ← hvdef, hu]
    · rw [mat_nsElt_mulVec_inr, mulVec_add, ← hudef, ← hvdef, hNu]
  · rw [mat_nsElt_mulVec_of_eq_zero 0 (single_apply_of_not_mem ht (inl_mem_coords 0))
      (single_apply_of_not_mem ht (inr_mem_coords 0))]
    obtain ⟨x, hxdef⟩ : ∃ x, x = mat (k + 2) K s *ᵥ Pi.single t 1 := ⟨_, rfl⟩
    rw [← hxdef]
    have hxv : form x v = 0 := by
      rw [hxdef, hvdef, form_mulVec, form_single_right, par_inl,
        single_apply_of_not_mem ht (inr_mem_coords 0), zero_mul]
    have hxu : form x u = 0 := by
      rw [hxdef, hudef, form_mulVec, form_single_right, par_inr,
        single_apply_of_not_mem ht (inl_mem_coords 0), zero_mul]
    rw [hvd, form_add_right, form_smul_right, form_smul_right] at hxv
    rw [hud, form_add_right, form_smul_right, form_smul_right] at hxu
    have hX : form x (Pi.single (Sum.inl j) 1) = 0 := by
      linear_combination (α + β) * hxv + β * hxu - form x (Pi.single (Sum.inl j) 1) * hq -
        (β ^ 2 * form x (Pi.single (Sum.inl j) 1) +
          (α * β + β ^ 2) * form x (Pi.single (Sum.inr j) 1)) * h2
    have hY : form x (Pi.single (Sum.inr j) 1) = 0 := by
      linear_combination β * hxv + α * hxu - form x (Pi.single (Sum.inr j) 1) * hq -
        (α * β * form x (Pi.single (Sum.inl j) 1) +
          β ^ 2 * form x (Pi.single (Sum.inr j) 1)) * h2
    rw [form_single_right, par_inl, sgn_inr] at hX
    rw [form_single_right, par_inr, sgn_inl, mul_one] at hY
    exact (mat_nsElt_mulVec_of_eq_zero j hY (by linear_combination -hX)).symm

theorem quad_eq_zero_iff (hK : Nat.card K = 2) (α β : K) :
    α * (α + β) - β * β = 0 ↔ α = 0 ∧ β = 0 := by
  rcases eq_zero_or_eq_one_of_natCard_two hK α with rfl | rfl <;>
    rcases eq_zero_or_eq_one_of_natCard_two hK β with rfl | rfl <;>
    simp [CharTwo.add_self_eq_zero]

omit [CharP K 2] in
theorem smul_add_smul_supp {n : ℕ} (i : Fin n) (α β : K) :
    ∀ r ∉ coords i, (α • Pi.single (Sum.inl i) 1 + β • Pi.single (Sum.inr i) 1 :
      Fin n ⊕ Fin n → K) r = 0 := fun r hr => by
  simp [single_supp (inl_mem_coords i) r hr, single_supp (inr_mem_coords i) r hr]

omit [CharP K 2] in
theorem form_planes_eq_zero {n : ℕ} {i j : Fin n} (hij : i ≠ j) (α β γ δ : K) :
    form (α • Pi.single (Sum.inl i) 1 + β • Pi.single (Sum.inr i) 1)
      (γ • Pi.single (Sum.inl j) 1 + δ • Pi.single (Sum.inr j) 1) = 0 :=
  form_eq_zero_of_supp (parClosed_coords j)
    (fun a ha => smul_add_smul_supp i α β a fun h => by
      rcases mem_coords.1 ha with rfl | rfl <;> rcases mem_coords.1 h with h' | h' <;> simp_all)
    (smul_add_smul_supp j γ δ)

theorem mat_nsElt_mulVec_smul_add_smul {n : ℕ} (j : Fin n) (α β : K) :
    mat n K (nsElt j) *ᵥ (α • Pi.single (Sum.inl j) 1 + β • Pi.single (Sum.inr j) 1) =
      β • Pi.single (Sum.inl j) 1 + (α + β) • Pi.single (Sum.inr j) 1 := by
  rw [mulVec_add, mulVec_smul, mulVec_smul, mat_nsElt_mulVec_inl, mat_nsElt_mulVec_inr]
  funext r
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem exists_mul_nsElt_eq (hK : Nat.card K = 2) {s : StatedSp (k + 2) K}
    (hs : s * (nsElt 0 * nsElt 1) = nsElt 0 * nsElt 1 * s) :
    ∃ j : Fin (k + 2), (j = 0 ∨ j = 1) ∧ s * nsElt 0 = nsElt j * s := by
  have hsg : ∀ x, mat (k + 2) K s *ᵥ (mat (k + 2) K (nsElt 0 * nsElt 1) *ᵥ x) =
      mat (k + 2) K (nsElt 0 * nsElt 1) *ᵥ (mat (k + 2) K s *ᵥ x) := fun x => by
    rw [mulVec_mulVec, ← map_mul, hs, map_mul, ← mulVec_mulVec]
  obtain ⟨v, hvdef⟩ : ∃ v, v = mat (k + 2) K s *ᵥ Pi.single (Sum.inl 0) 1 := ⟨_, rfl⟩
  obtain ⟨u, hudef⟩ : ∃ u, u = mat (k + 2) K s *ᵥ Pi.single (Sum.inr 0) 1 := ⟨_, rfl⟩
  have hu : u = mat (k + 2) K (nsElt 0 * nsElt 1) *ᵥ v := by
    rw [hudef, ← mulVec_nsElt_zero_mul_one_inl (K := K) (k := k) (Or.inl rfl), hsg, ← hvdef]
  have hvU : ∀ r ∉ coords (0 : Fin (k + 2)) ∪ coords 1, v r = 0 := by
    have hv' : v = mat (k + 2) K (nsElt 0 * nsElt 1) *ᵥ u - u := by
      rw [hvdef, hudef, ← hsg, ← mulVec_sub, mulVec_nsElt_zero_mul_one_inr (Or.inl rfl),
        add_sub_cancel_right]
    intro r hr
    rw [hv', Pi.sub_apply, mulVec_apply_of_isSupp (M := mat (k + 2) K (nsElt 0 * nsElt 1))
      nsElt_zero_mul_one_mem_suppGroup u hr, sub_self]
  have h01 := zero_ne_one_fin (k := k)
  obtain ⟨a, ha⟩ : ∃ a, a = v (Sum.inl 0) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = v (Sum.inr 0) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = v (Sum.inl 1) := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = v (Sum.inr 1) := ⟨_, rfl⟩
  have hv01 : v = (a • Pi.single (Sum.inl 0) 1 + b • Pi.single (Sum.inr 0) 1) +
      (c • Pi.single (Sum.inl 1) 1 + d • Pi.single (Sum.inr 1) 1) := by
    rw [ha, hb, hc, hd]
    funext r
    rcases r with i | i <;> by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;>
      simp_all [mem_coords]
  have hu01 : u = (b • Pi.single (Sum.inl 0) 1 + (a + b) • Pi.single (Sum.inr 0) 1) +
      (d • Pi.single (Sum.inl 1) 1 + (c + d) • Pi.single (Sum.inr 1) 1) := by
    rw [hu, hv01, mulVec_add,
      mulVec_nsElt_zero_mul_one_of_supp (Or.inl rfl) (smul_add_smul_supp 0 _ _),
      mulVec_nsElt_zero_mul_one_of_supp (Or.inr rfl) (smul_add_smul_supp 1 _ _),
      mat_nsElt_mulVec_smul_add_smul, mat_nsElt_mulVec_smul_add_smul]
  have hq : (a * (a + b) - b * b) + (c * (c + d) - d * d) = 1 := by
    have h := form_mulVec s (Pi.single (Sum.inl 0) 1) (Pi.single (Sum.inr 0) 1)
    rw [form_single_inl_inr, ← hvdef, ← hudef, hv01, hu01] at h
    simp only [form_add_right, form_smul_right, form_single_right, par_inl, par_inr, sgn_inl,
      sgn_inr, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, Sum.inl.injEq,
      Sum.inr.injEq, reduceCtorEq, h01, h01.symm, ite_true, ite_false] at h
    linear_combination h
  rcases eq_zero_or_eq_one_of_natCard_two hK (a * (a + b) - b * b) with h0 | h0
  · obtain ⟨ha0, hb0⟩ := (quad_eq_zero_iff hK _ _).mp h0
    refine ⟨1, Or.inr rfl, mul_nsElt_zero_eq_of_supp (Or.inr rfl) hs ?_⟩
    rw [← hvdef]
    intro r hr
    by_cases hr0 : r ∈ coords (0 : Fin (k + 2))
    · rcases mem_coords.1 hr0 with rfl | rfl
      · rw [← ha, ha0]
      · rw [← hb, hb0]
    · exact hvU r (by rintro (h | h) <;> contradiction)
  · rw [h0] at hq
    have h1 : c * (c + d) - d * d = 0 := by linear_combination hq
    obtain ⟨hc0, hd0⟩ := (quad_eq_zero_iff hK _ _).mp h1
    refine ⟨0, Or.inl rfl, mul_nsElt_zero_eq_of_supp (Or.inl rfl) hs ?_⟩
    rw [← hvdef]
    intro r hr
    by_cases hr1 : r ∈ coords (1 : Fin (k + 2))
    · rcases mem_coords.1 hr1 with rfl | rfl
      · rw [← hc, hc0]
      · rw [← hd, hd0]
    · exact hvU r (by rintro (h | h) <;> contradiction)

end Dichotomy

section Swap

theorem conj_commutator_eq_of_perm {G : Type*} [Group G] {a b x y : G}
    (hx : (x * a * x⁻¹ = a ∧ x * b * x⁻¹ = b) ∨ (x * a * x⁻¹ = b ∧ x * b * x⁻¹ = a))
    (hy : (y * a * y⁻¹ = a ∧ y * b * y⁻¹ = b) ∨ (y * a * y⁻¹ = b ∧ y * b * y⁻¹ = a)) :
    (x * y * x⁻¹ * y⁻¹) * a * (x * y * x⁻¹ * y⁻¹)⁻¹ = a := by
  have ci : ∀ {z c d : G}, z * c * z⁻¹ = d → z⁻¹ * d * z = c := fun {z c d} h => by
    rw [← h]
    group
  have e : (x * y * x⁻¹ * y⁻¹) * a * (x * y * x⁻¹ * y⁻¹)⁻¹ =
      x * (y * (x⁻¹ * (y⁻¹ * a * y) * x) * y⁻¹) * x⁻¹ := by group
  rw [e]
  rcases hx with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩ <;> rcases hy with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩
  · rw [ci hy1, ci hx1, hy1, hx1]
  · rw [ci hy2, ci hx2, hy2, hx1]
  · rw [ci hy1, ci hx2, hy2, hx2]
  · rw [ci hy2, ci hx1, hy1, hx2]

variable (K k) in
@[expose] noncomputable def planeSwap : StatedSp (k + 2) K :=
  permSp K (Equiv.swap (0 : Fin (k + 2)) 1)

theorem planeSwap_conj_nsElt_zero :
    planeSwap K k * nsElt 0 * (planeSwap K k)⁻¹ = nsElt 1 := by
  have h := conj_permSp_longBlock (K := K) (Equiv.swap (0 : Fin (k + 2)) 1) 0 zThreeSL
  rwa [Equiv.swap_apply_left] at h

theorem planeSwap_conj_nsElt_one :
    planeSwap K k * nsElt 1 * (planeSwap K k)⁻¹ = nsElt 0 := by
  have h := conj_permSp_longBlock (K := K) (Equiv.swap (0 : Fin (k + 2)) 1) 1 zThreeSL
  rwa [Equiv.swap_apply_right] at h

theorem planeSwap_mem_suppGroup :
    planeSwap K k ∈ suppGroup (coords (0 : Fin (k + 2)) ∪ coords 1) := by
  rw [mem_suppGroup_iff parClosed_coords_union]
  intro t ht r
  rw [planeSwap, mat_permSp, spIncl_apply]
  have hfix : Sum.map (Equiv.swap (0 : Fin (k + 2)) 1) (Equiv.swap (0 : Fin (k + 2)) 1) t = t := by
    rcases t with i | i <;>
    · have hi0 : i ≠ 0 := fun h => ht (by simp [h, mem_coords])
      have hi1 : i ≠ 1 := fun h => ht (by simp [h, mem_coords])
      simp [Equiv.swap_apply_of_ne_of_ne hi0 hi1]
  rw [hfix, Matrix.one_apply]

theorem commute_planeSwap {y : StatedSp (k + 2) K}
    (hy : y ∈ complSp K (0 : Fin (k + 2)) ⊓ complSp K 1) : Commute (planeSwap K k) y :=
  commute_suppGroup_compl planeSwap_mem_suppGroup (inf_complSp_le_suppGroup hy)

variable [CharP K 2]

theorem exists_eq_mul_mul_of_commute (hK : Nat.card K = 2) {s : StatedSp (k + 2) K}
    (h0 : s * nsElt 0 = nsElt 0 * s) (h1 : s * nsElt 1 = nsElt 1 * s) :
    ∃ a ∈ nsTorusSp K (0 : Fin (k + 2)), ∃ b ∈ nsTorusSp K (1 : Fin (k + 2)),
      ∃ y ∈ complSp K (0 : Fin (k + 2)) ⊓ complSp K 1, s = a * b * y := by
  obtain ⟨a, ha, y₀, hy₀, rfl⟩ := exists_eq_mul_of_commute_nsElt hK h0
  have hcomm := commute_nsElt_zero_one (K := K) (k := k)
  have ha1 : Commute a (nsElt 1) := by
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact hcomm.zpow_left m
  have hy₀1 : y₀ * nsElt 1 = nsElt 1 * y₀ := by
    have h : a * (y₀ * nsElt 1) = a * (nsElt 1 * y₀) := by
      rw [← mul_assoc, h1, ← mul_assoc, ← ha1.eq, mul_assoc]
    exact mul_left_cancel h
  obtain ⟨b, hb, y, hy, rfl⟩ := exists_eq_mul_of_commute_nsElt hK hy₀1
  have hb0 : b ∈ complSp K (0 : Fin (k + 2)) := by
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact zpow_mem (nsElt_mem_complSp zero_ne_one_fin.symm) m
  have hy0 : y ∈ complSp K (0 : Fin (k + 2)) := by
    have := mul_mem (inv_mem hb0) hy₀
    rwa [inv_mul_cancel_left] at this
  exact ⟨a, ha, b, hb, y, ⟨hy0, hy⟩, by rw [mul_assoc]⟩

end Swap

section Layer

variable [CharP K 2]

omit [CharP K 2] in
theorem commute_nsTorusSp_zero_one {a b : StatedSp (k + 2) K}
    (ha : a ∈ nsTorusSp K (0 : Fin (k + 2))) (hb : b ∈ nsTorusSp K (1 : Fin (k + 2))) :
    Commute a b := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨m', rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  exact (commute_nsElt_zero_one (K := K) (k := k)).zpow_zpow m m'

omit [CharP K 2] in
theorem commute_mul_mul {a b a' b' : StatedSp (k + 2) K}
    (ha : a ∈ nsTorusSp K (0 : Fin (k + 2))) (hb : b ∈ nsTorusSp K (1 : Fin (k + 2)))
    (ha' : a' ∈ nsTorusSp K (0 : Fin (k + 2))) (hb' : b' ∈ nsTorusSp K (1 : Fin (k + 2))) :
    Commute (a * b) (a' * b') := by
  have h00 : Commute a a' :=
    Subgroup.mem_centralizer_iff.mp (nsTorusSp_le_centralizer_self 0 ha') a ha
  have h11 : Commute b b' :=
    Subgroup.mem_centralizer_iff.mp (nsTorusSp_le_centralizer_self 1 hb') b hb
  exact ((h00.mul_right (commute_nsTorusSp_zero_one ha hb')).mul_left
    ((commute_nsTorusSp_zero_one ha' hb).symm.mul_right h11))

omit [CharP K 2] in
theorem commute_mul_of_mem_inf {a b y : StatedSp (k + 2) K}
    (ha : a ∈ nsTorusSp K (0 : Fin (k + 2))) (hb : b ∈ nsTorusSp K (1 : Fin (k + 2)))
    (hy : y ∈ complSp K (0 : Fin (k + 2)) ⊓ complSp K 1) : Commute (a * b) y :=
  Commute.mul_left (Subgroup.mem_centralizer_iff.mp (complSp_le_centralizer_nsTorusSp 0 hy.1) a ha)
    (Subgroup.mem_centralizer_iff.mp (complSp_le_centralizer_nsTorusSp 1 hy.2) b hb)

theorem commutator_mem_of_commute_nsElt_zero_one (hK : Nat.card K = 2)
    {s s' : StatedSp (k + 2) K} (h0 : s * nsElt 0 = nsElt 0 * s) (h1 : s * nsElt 1 = nsElt 1 * s)
    (h0' : s' * nsElt 0 = nsElt 0 * s') (h1' : s' * nsElt 1 = nsElt 1 * s') :
    s * s' * s⁻¹ * s'⁻¹ ∈
      ⁅complSp K (0 : Fin (k + 2)) ⊓ complSp K 1, complSp K (0 : Fin (k + 2)) ⊓ complSp K 1⁆ := by
  obtain ⟨a, ha, b, hb, y, hy, rfl⟩ := exists_eq_mul_mul_of_commute hK h0 h1
  obtain ⟨a', ha', b', hb', y', hy', rfl⟩ := exists_eq_mul_mul_of_commute hK h0' h1'
  rw [commutatorElement_eq_of_commute (commute_mul_mul ha hb ha' hb')
    (commute_mul_of_mem_inf ha hb hy) (commute_mul_of_mem_inf ha hb hy')
    (commute_mul_of_mem_inf ha' hb' hy) (commute_mul_of_mem_inf ha' hb' hy'),
    ← commutatorElement_def]
  exact Subgroup.commutator_mem_commutator hy hy'

theorem perm_of_commute_nsElt_zero_mul_one (hK : Nat.card K = 2) {x : StatedSp (k + 2) K}
    (hx : x * (nsElt 0 * nsElt 1) = nsElt 0 * nsElt 1 * x) :
    (x * nsElt 0 * x⁻¹ = nsElt 0 ∧ x * nsElt 1 * x⁻¹ = nsElt 1) ∨
      (x * nsElt 0 * x⁻¹ = nsElt 1 ∧ x * nsElt 1 * x⁻¹ = nsElt 0) := by
  obtain ⟨j, hj, hxj⟩ := exists_mul_nsElt_eq hK hx
  have hconj0 : x * nsElt 0 * x⁻¹ = nsElt j := by rw [hxj]; group
  have hg : x * (nsElt 0 * nsElt 1) * x⁻¹ = nsElt 0 * nsElt 1 := by rw [hx]; group
  have hconj1 : x * nsElt 1 * x⁻¹ = (nsElt j)⁻¹ * (nsElt 0 * nsElt 1) := by
    rw [← hconj0, ← hg]
    group
  rcases hj with rfl | rfl
  · refine Or.inl ⟨hconj0, ?_⟩
    rw [hconj1]
    group
  · refine Or.inr ⟨hconj0, ?_⟩
    rw [hconj1, (commute_nsElt_zero_one (K := K) (k := k)).eq]
    group

theorem commutator_commute_nsElt (hK : Nat.card K = 2) {x y : StatedSp (k + 2) K}
    (hx : x * (nsElt 0 * nsElt 1) = nsElt 0 * nsElt 1 * x)
    (hy : y * (nsElt 0 * nsElt 1) = nsElt 0 * nsElt 1 * y) :
    (x * y * x⁻¹ * y⁻¹) * nsElt 0 = nsElt 0 * (x * y * x⁻¹ * y⁻¹) ∧
      (x * y * x⁻¹ * y⁻¹) * nsElt 1 = nsElt 1 * (x * y * x⁻¹ * y⁻¹) := by
  have px := perm_of_commute_nsElt_zero_mul_one hK hx
  have py := perm_of_commute_nsElt_zero_mul_one hK hy
  have h0 := conj_commutator_eq_of_perm px py
  have h1 := conj_commutator_eq_of_perm (px.imp And.symm And.symm) (py.imp And.symm And.symm)
  have fix : ∀ {c N : StatedSp (k + 2) K}, c * N * c⁻¹ = N → c * N = N * c := fun {c N} h => by
    calc c * N = c * N * c⁻¹ * c := by group
      _ = N * c := by rw [h]
  exact ⟨fix h0, fix h1⟩

theorem conj_mem_commutator_inf (hK : Nat.card K = 2) {h : StatedSp (k + 2) K}
    (h0 : h * nsElt 0 = nsElt 0 * h) (h1 : h * nsElt 1 = nsElt 1 * h) {d : StatedSp (k + 2) K}
    (hd : d ∈ ⁅complSp K (0 : Fin (k + 2)) ⊓ complSp K 1,
      complSp K (0 : Fin (k + 2)) ⊓ complSp K 1⁆) :
    h * d * h⁻¹ ∈ ⁅complSp K (0 : Fin (k + 2)) ⊓ complSp K 1,
      complSp K (0 : Fin (k + 2)) ⊓ complSp K 1⁆ := by
  obtain ⟨a, ha, b, hb, y, hy, rfl⟩ := exists_eq_mul_mul_of_commute hK h0 h1
  have hyd : y * d * y⁻¹ ∈ ⁅complSp K (0 : Fin (k + 2)) ⊓ complSp K 1,
      complSp K (0 : Fin (k + 2)) ⊓ complSp K 1⁆ := by
    have hmap := TableBSymp.map_conj_eq_self hy
    have : ⁅complSp K (0 : Fin (k + 2)) ⊓ complSp K 1,
        complSp K (0 : Fin (k + 2)) ⊓ complSp K 1⁆.map (MulAut.conj y).toMonoidHom =
        ⁅complSp K (0 : Fin (k + 2)) ⊓ complSp K 1,
          complSp K (0 : Fin (k + 2)) ⊓ complSp K 1⁆ := by
      rw [Subgroup.map_commutator, hmap]
    rw [← this]
    exact ⟨d, hd, rfl⟩
  have hc := commute_mul_of_mem_inf ha hb (Subgroup.commutator_le_self _ hyd)
  have e : a * b * y * d * (a * b * y)⁻¹ = y * d * y⁻¹ :=
    calc a * b * y * d * (a * b * y)⁻¹ = (a * b) * (y * d * y⁻¹) * (a * b)⁻¹ := by group
      _ = y * d * y⁻¹ := by rw [hc.eq, mul_inv_cancel_right]
  rw [e]
  exact hyd

end Layer

section Main

variable [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem inf_complSp_le_centralizer :
    complSp K (0 : Fin (k + 2)) ⊓ complSp K 1 ≤
      Subgroup.centralizer {nsElt (K := K) (n := k + 2) 0 * nsElt 1} := by
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h0 : nsElt 0 * y = y * nsElt 0 :=
    Subgroup.mem_centralizer_iff.mp (complSp_le_centralizer_nsTorusSp 0 hy.1) _
      (nsElt_mem_nsTorusSp 0)
  have h1 : nsElt 1 * y = y * nsElt 1 :=
    Subgroup.mem_centralizer_iff.mp (complSp_le_centralizer_nsTorusSp 1 hy.2) _
      (nsElt_mem_nsTorusSp 1)
  rw [← mul_assoc, ← h0, mul_assoc, ← h1, ← mul_assoc]

omit [Finite K] [CharP K 2] in
theorem planeSwap_mul_commute {x : StatedSp (k + 2) K}
    (h0 : x * nsElt 0 * x⁻¹ = nsElt 1) (h1 : x * nsElt 1 * x⁻¹ = nsElt 0) :
    planeSwap K k * x * nsElt 0 = nsElt 0 * (planeSwap K k * x) ∧
      planeSwap K k * x * nsElt 1 = nsElt 1 * (planeSwap K k * x) := by
  have e0 : (planeSwap K k * x) * nsElt 0 * (planeSwap K k * x)⁻¹ = nsElt 0 := by
    rw [show (planeSwap K k * x) * nsElt 0 * (planeSwap K k * x)⁻¹ =
      planeSwap K k * (x * nsElt 0 * x⁻¹) * (planeSwap K k)⁻¹ by group, h0,
      planeSwap_conj_nsElt_one]
  have e1 : (planeSwap K k * x) * nsElt 1 * (planeSwap K k * x)⁻¹ = nsElt 1 := by
    rw [show (planeSwap K k * x) * nsElt 1 * (planeSwap K k * x)⁻¹ =
      planeSwap K k * (x * nsElt 1 * x⁻¹) * (planeSwap K k)⁻¹ by group, h1,
      planeSwap_conj_nsElt_zero]
  constructor
  · calc planeSwap K k * x * nsElt 0 =
        (planeSwap K k * x) * nsElt 0 * (planeSwap K k * x)⁻¹ * (planeSwap K k * x) := by group
      _ = nsElt 0 * (planeSwap K k * x) := by rw [e0]
  · calc planeSwap K k * x * nsElt 1 =
        (planeSwap K k * x) * nsElt 1 * (planeSwap K k * x)⁻¹ * (planeSwap K k * x) := by group
      _ = nsElt 1 * (planeSwap K k * x) := by rw [e1]

theorem layer_centralizer_nsElt_zero_mul_one (hK : Nat.card K = 2) (hk : 2 ≤ k) :
    LargeEvenLayer (Subgroup.centralizer {nsElt (K := K) (n := k + 2) 0 * nsElt 1}) =
        ⁅complSp K (0 : Fin (k + 2)) ⊓ complSp K 1, complSp K (0 : Fin (k + 2)) ⊓ complSp K 1⁆ ∧
      IsComponentOf
        ⁅complSp K (0 : Fin (k + 2)) ⊓ complSp K 1, complSp K (0 : Fin (k + 2)) ⊓ complSp K 1⁆
        (Subgroup.centralizer {nsElt (K := K) (n := k + 2) 0 * nsElt 1}) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_inf_complSp (K := K) (k := k)
  refine largeEvenLayer_eq_of_commutator_commutator_mem
    ((Subgroup.commutator_le_self _).trans inf_complSp_le_centralizer) ?_ ?_
    (isQuasisimple_commutator_of_mulEquiv hK hk e)
  · intro h hh d hd
    have hx := Subgroup.mem_centralizer_singleton_iff.mp hh
    rcases perm_of_commute_nsElt_zero_mul_one hK hx with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · have fix : ∀ {N : StatedSp (k + 2) K}, h * N * h⁻¹ = N → h * N = N * h := fun {N} hN => by
        calc h * N = h * N * h⁻¹ * h := by group
          _ = N * h := by rw [hN]
      exact conj_mem_commutator_inf hK (fix h0) (fix h1) hd
    · obtain ⟨c0, c1⟩ := planeSwap_mul_commute h0 h1
      have hwd := conj_mem_commutator_inf hK c0 c1 hd
      have hwc := commute_planeSwap (K := K) (k := k)
        (Subgroup.commutator_le_self _ hwd)
      rw [show h * d * h⁻¹ = (planeSwap K k)⁻¹ * ((planeSwap K k * h) * d *
        (planeSwap K k * h)⁻¹) * planeSwap K k by group, mul_assoc, ← hwc.eq, ← mul_assoc,
        inv_mul_cancel, one_mul]
      exact hwd
  · have hle : ⁅Subgroup.centralizer {nsElt (K := K) (n := k + 2) 0 * nsElt 1},
        Subgroup.centralizer {nsElt (K := K) (n := k + 2) 0 * nsElt 1}⁆ ≤
        Subgroup.centralizer {nsElt (K := K) (n := k + 2) 0} ⊓
          Subgroup.centralizer {nsElt (K := K) (n := k + 2) 1} := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      obtain ⟨c0, c1⟩ := commutator_commute_nsElt hK (Subgroup.mem_centralizer_singleton_iff.mp hx)
        (Subgroup.mem_centralizer_singleton_iff.mp hy)
      rw [commutatorElement_def]
      exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr c0,
        Subgroup.mem_centralizer_singleton_iff.mpr c1⟩
    intro g hg g' hg'
    obtain ⟨h0, h1⟩ := hle hg
    obtain ⟨h0', h1'⟩ := hle hg'
    exact commutator_mem_of_commute_nsElt_zero_one hK
      (Subgroup.mem_centralizer_singleton_iff.mp h0) (Subgroup.mem_centralizer_singleton_iff.mp h1)
      (Subgroup.mem_centralizer_singleton_iff.mp h0')
      (Subgroup.mem_centralizer_singleton_iff.mp h1')

theorem mem_suppGroup_of_commute_nsElt_zero_mul_one (hK : Nat.card K = 2) (hk : 2 ≤ k)
    {s : StatedSp (k + 2) K}
    (hs : s ∈ Subgroup.centralizer {nsElt (K := K) (n := k + 2) 0 * nsElt 1})
    (hsD : ∀ j ∈ ⁅complSp K (0 : Fin (k + 2)) ⊓ complSp K 1,
      complSp K (0 : Fin (k + 2)) ⊓ complSp K 1⁆, s * j = j * s) :
    s ∈ suppGroup (coords (0 : Fin (k + 2)) ∪ coords 1) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_inf_complSp (K := K) (k := k)
  have key : ∀ s' : StatedSp (k + 2) K, s' * nsElt 0 = nsElt 0 * s' →
      s' * nsElt 1 = nsElt 1 * s' →
      (∀ j ∈ ⁅complSp K (0 : Fin (k + 2)) ⊓ complSp K 1,
        complSp K (0 : Fin (k + 2)) ⊓ complSp K 1⁆, s' * j = j * s') →
      s' ∈ suppGroup (coords (0 : Fin (k + 2)) ∪ coords 1) := by
    intro s' h0 h1 hD
    obtain ⟨a, ha, b, hb, y, hy, rfl⟩ := exists_eq_mul_mul_of_commute hK h0 h1
    have hy1 : y = 1 := by
      refine eq_one_of_commute_commutator_of_mulEquiv hK hk e hy fun j hj => ?_
      have hc := commute_mul_of_mem_inf ha hb (Subgroup.commutator_le_self _ hj)
      have h2 := hD j hj
      have : a * b * (y * j) = a * b * (j * y) := by
        calc a * b * (y * j) = a * b * y * j := by group
          _ = j * (a * b * y) := h2
          _ = (j * (a * b)) * y := by group
          _ = a * b * (j * y) := by rw [← hc.eq]; group
      exact mul_left_cancel this
    rw [hy1, mul_one]
    exact mul_mem (Subgroup.zpowers_le.mpr (nsElt_mem_suppGroup_union (Or.inl rfl)) ha)
      (Subgroup.zpowers_le.mpr (nsElt_mem_suppGroup_union (Or.inr rfl)) hb)
  have hx := Subgroup.mem_centralizer_singleton_iff.mp hs
  rcases perm_of_commute_nsElt_zero_mul_one hK hx with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have fix : ∀ {N : StatedSp (k + 2) K}, s * N * s⁻¹ = N → s * N = N * s := fun {N} hN => by
      calc s * N = s * N * s⁻¹ * s := by group
        _ = N * s := by rw [hN]
    exact key s (fix h0) (fix h1) hsD
  · obtain ⟨c0, c1⟩ := planeSwap_mul_commute h0 h1
    have hw := key (planeSwap K k * s) c0 c1 fun j hj => by
      have hwc := commute_planeSwap (K := K) (k := k) (Subgroup.commutator_le_self _ hj)
      rw [mul_assoc, hsD j hj, ← mul_assoc, hwc.eq, mul_assoc]
    rw [show s = (planeSwap K k)⁻¹ * (planeSwap K k * s) by group]
    exact mul_mem (inv_mem planeSwap_mem_suppGroup) hw

omit [Finite K] in
theorem eq_zero_of_mulVec_nsElt_zero_mul_one {v : Fin (k + 2) ⊕ Fin (k + 2) → K}
    (hv : mat (k + 2) K (nsElt 0 * nsElt 1) *ᵥ v = v) :
    ∀ r ∈ coords (0 : Fin (k + 2)) ∪ coords 1, v r = 0 := by
  rintro r (hr | hr)
  · obtain ⟨h1, h2⟩ := eq_zero_of_mulVec_eq_self 0
      (mulVec_nsElt_zero_mul_one_inl (Or.inl rfl)) (mulVec_nsElt_zero_mul_one_inr (Or.inl rfl)) hv
    rcases mem_coords.1 hr with rfl | rfl
    · exact h1
    · exact h2
  · obtain ⟨h1, h2⟩ := eq_zero_of_mulVec_eq_self 1
      (mulVec_nsElt_zero_mul_one_inl (Or.inr rfl)) (mulVec_nsElt_zero_mul_one_inr (Or.inr rfl)) hv
    rcases mem_coords.1 hr with rfl | rfl
    · exact h1
    · exact h2

end Main

end CFSG.StandardType.TwoThreeOrth
