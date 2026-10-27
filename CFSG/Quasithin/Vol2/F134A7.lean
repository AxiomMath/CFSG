module

public import CFSG.Quasithin.Vol2.F134Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.Quasithin.F134

open Equiv MulAction

@[expose] def a7c₁ : alternatingGroup (Fin 7) :=
  ⟨List.formPerm [0, 1, 2], Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def a7c₂ : alternatingGroup (Fin 7) :=
  ⟨List.formPerm [3, 4, 5], Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def a7P₀ : Subgroup (alternatingGroup (Fin 7)) :=
  Subgroup.zpowers a7c₁ ⊔ Subgroup.zpowers a7c₂

theorem a7_smul_def (g : alternatingGroup (Fin 7)) (x : Fin 7) :
    g • x = (g : Perm (Fin 7)) x := rfl

theorem a7c₁_apply : ∀ x : Fin 7, (a7c₁ : Perm (Fin 7)) x =
    if x = 0 then 1 else if x = 1 then 2 else if x = 2 then 0 else x := by decide

theorem a7c₂_apply : ∀ x : Fin 7, (a7c₂ : Perm (Fin 7)) x =
    if x = 3 then 4 else if x = 4 then 5 else if x = 5 then 3 else x := by decide

theorem orderOf_a7c₁ : orderOf a7c₁ = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime (Subtype.ext ?_) ?_
  · show (List.formPerm [0, 1, 2] : Perm (Fin 7)) ^ 3 = 1
    decide
  · intro h
    have := congrArg (fun g : alternatingGroup (Fin 7) => (g : Perm (Fin 7)) 0) h
    revert this
    decide

theorem orderOf_a7c₂ : orderOf a7c₂ = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime (Subtype.ext ?_) ?_
  · show (List.formPerm [3, 4, 5] : Perm (Fin 7)) ^ 3 = 1
    decide
  · intro h
    have := congrArg (fun g : alternatingGroup (Fin 7) => (g : Perm (Fin 7)) 3) h
    revert this
    decide

theorem a7c_comm : a7c₁ * a7c₂ = a7c₂ * a7c₁ := Subtype.ext (by
  show (List.formPerm [0, 1, 2] : Perm (Fin 7)) * List.formPerm [3, 4, 5] =
    List.formPerm [3, 4, 5] * List.formPerm [0, 1, 2]
  decide)

theorem a7P₀_fix_six {p : alternatingGroup (Fin 7)} (hp : p ∈ a7P₀) :
    (p : Perm (Fin 7)) 6 = 6 := by
  have hle : a7P₀ ≤ stabilizer (alternatingGroup (Fin 7)) (6 : Fin 7) := by
    refine sup_le ?_ ?_ <;> rw [Subgroup.zpowers_le, mem_stabilizer_iff, a7_smul_def]
    · rw [a7c₁_apply]
      decide
    · rw [a7c₂_apply]
      decide
  exact hle hp

theorem a7_zpowers_fix {g : alternatingGroup (Fin 7)} :
    (g ∈ Subgroup.zpowers a7c₁ → ∀ x : Fin 7, x ∈ ({3, 4, 5, 6} : Finset (Fin 7)) →
      (g : Perm (Fin 7)) x = x) ∧
    (g ∈ Subgroup.zpowers a7c₂ → ∀ x : Fin 7, x ∈ ({0, 1, 2, 6} : Finset (Fin 7)) →
      (g : Perm (Fin 7)) x = x) := by
  constructor
  · intro hg x hx
    have hle : Subgroup.zpowers a7c₁ ≤ stabilizer (alternatingGroup (Fin 7)) x := by
      rw [Subgroup.zpowers_le, mem_stabilizer_iff, a7_smul_def, a7c₁_apply]
      revert hx x
      decide
    exact hle hg
  · intro hg x hx
    have hle : Subgroup.zpowers a7c₂ ≤ stabilizer (alternatingGroup (Fin 7)) x := by
      rw [Subgroup.zpowers_le, mem_stabilizer_iff, a7_smul_def, a7c₂_apply]
      revert hx x
      decide
    exact hle hg

theorem card_a7P₀ : Nat.card a7P₀ = 9 := by
  have hdisj : Disjoint (Subgroup.zpowers a7c₂) (Subgroup.zpowers a7c₁) := by
    rw [Subgroup.disjoint_def]
    intro g h2 h1
    apply Subtype.ext
    refine Equiv.ext fun x => ?_
    have hf1 := a7_zpowers_fix.1 h1
    have hf2 := a7_zpowers_fix.2 h2
    show (g : Perm (Fin 7)) x = x
    fin_cases x
    · exact hf2 0 (by decide)
    · exact hf2 1 (by decide)
    · exact hf2 2 (by decide)
    · exact hf1 3 (by decide)
    · exact hf1 4 (by decide)
    · exact hf1 5 (by decide)
    · exact hf1 6 (by decide)
  have hnorm : Subgroup.zpowers a7c₁ ≤
      Subgroup.normalizer (Subgroup.zpowers a7c₂ : Set (alternatingGroup (Fin 7))) := by
    refine le_trans ?_ (CFSG.Quasithin.P134.centralizer_le_normalizer_self _)
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact ((Commute.zpow_left a7c_comm.symm k)).eq
  rw [a7P₀, sup_comm, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
    hnorm hdisj, Nat.card_zpowers, Nat.card_zpowers, orderOf_a7c₁, orderOf_a7c₂]

theorem eq_one_or_eq_swap {α : Type*} [DecidableEq α] {σ : Perm α} {u v : α} (huv : u ≠ v)
    (h : ∀ x, x ≠ u → x ≠ v → σ x = x) : σ = 1 ∨ σ = swap u v := by
  have hu : σ u = u ∨ σ u = v := by
    by_contra hc
    rw [not_or] at hc
    exact hc.1 (σ.injective (h (σ u) hc.1 hc.2))
  have hv : σ v = u ∨ σ v = v := by
    by_contra hc
    rw [not_or] at hc
    exact hc.2 (σ.injective (h (σ v) hc.1 hc.2))
  rcases hu with hu | hu
  · have hv' : σ v = v := hv.resolve_left fun h' => huv (σ.injective (hu.trans h'.symm))
    left
    refine Equiv.ext fun x => ?_
    by_cases hxu : x = u
    · rw [hxu, hu, Perm.one_apply]
    · by_cases hxv : x = v
      · rw [hxv, hv', Perm.one_apply]
      · rw [h x hxu hxv, Perm.one_apply]
  · have hv' : σ v = u := hv.resolve_right fun h' => huv (σ.injective (hu.trans h'.symm))
    right
    refine Equiv.ext fun x => ?_
    by_cases hxu : x = u
    · rw [hxu, hu, swap_apply_left]
    · by_cases hxv : x = v
      · rw [hxv, hv', swap_apply_right]
      · rw [h x hxu hxv, swap_apply_of_ne_of_ne hxu hxv]

theorem eq_one_of_sign_of_fix {σ : Perm (Fin 7)} (hσ : Perm.sign σ = 1) {u v : Fin 7}
    (huv : u ≠ v) (h : ∀ x, x ≠ u → x ≠ v → σ x = x) : σ = 1 := by
  rcases eq_one_or_eq_swap huv h with h1 | h1
  · exact h1
  · rw [h1, Perm.sign_swap huv] at hσ
    exact absurd hσ (by decide)

theorem a7_sub_smul {K : Subgroup (alternatingGroup (Fin 7))} (k : K) (x : Fin 7) :
    k • x = ((k : alternatingGroup (Fin 7)) : Perm (Fin 7)) x := rfl

theorem card_le_three_of_fix (K : Subgroup (alternatingGroup (Fin 7))) {a b c : Fin 7}
    (hbc : b ≠ c)
    (hK : ∀ k ∈ K, ∀ x, x ≠ a → x ≠ b → x ≠ c → (k : Perm (Fin 7)) x = x) :
    Nat.card K ≤ 3 := by
  have horb : orbit K a ⊆ {a, b, c} := by
    rintro _ ⟨k, rfl⟩
    change k • a ∈ ({a, b, c} : Set (Fin 7))
    rw [a7_sub_smul]
    by_contra hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
    have hy := hK k k.2 _ hne.1 hne.2.1 hne.2.2
    exact hne.1 (((k : alternatingGroup (Fin 7)) : Perm (Fin 7)).injective hy)
  have hstab : stabilizer K a = ⊥ := by
    rw [eq_bot_iff]
    intro k hk
    rw [mem_stabilizer_iff, a7_sub_smul] at hk
    rw [Subgroup.mem_bot]
    refine Subtype.ext (Subtype.ext (eq_one_of_sign_of_fix ((k : alternatingGroup (Fin 7)).2)
      hbc fun x hxb hxc => ?_))
    by_cases hxa : x = a
    · rw [hxa]
      exact hk
    · exact hK k k.2 x hxa hxb hxc
  have h1 := Subgroup.card_mul_index (stabilizer K a)
  rw [index_stabilizer, hstab, Subgroup.card_bot, one_mul] at h1
  rw [← h1]
  calc (orbit K a).ncard ≤ ({a, b, c} : Set (Fin 7)).ncard :=
        Set.ncard_le_ncard horb (Set.toFinite _)
    _ ≤ 3 := by
        refine (Set.ncard_insert_le _ _).trans ?_
        rw [Set.ncard_pair hbc]

theorem a7_orbit_closed (H : Subgroup (alternatingGroup (Fin 7))) {g : alternatingGroup (Fin 7)}
    (hg : g ∈ H) {x y : Fin 7} (hy : y ∈ orbit H x) : (g : Perm (Fin 7)) y ∈ orbit H x := by
  obtain ⟨h, rfl⟩ := hy
  refine ⟨⟨g, hg⟩ * h, ?_⟩
  change (⟨g, hg⟩ * h : H) • x = (g : Perm (Fin 7)) (h • x)
  rw [mul_smul]
  rfl

theorem a7_orbit_iff (H : Subgroup (alternatingGroup (Fin 7))) (hc₁ : a7c₁ ∈ H) (hc₂ : a7c₂ ∈ H)
    (x : Fin 7) :
    ((0 : Fin 7) ∈ orbit H x ↔ (1 : Fin 7) ∈ orbit H x) ∧
      ((1 : Fin 7) ∈ orbit H x ↔ (2 : Fin 7) ∈ orbit H x) ∧
      ((3 : Fin 7) ∈ orbit H x ↔ (4 : Fin 7) ∈ orbit H x) ∧
      ((4 : Fin 7) ∈ orbit H x ↔ (5 : Fin 7) ∈ orbit H x) := by
  have e01 : (a7c₁ : Perm (Fin 7)) 0 = 1 := by decide
  have e12 : (a7c₁ : Perm (Fin 7)) 1 = 2 := by decide
  have e20 : (a7c₁ : Perm (Fin 7)) 2 = 0 := by decide
  have e34 : (a7c₂ : Perm (Fin 7)) 3 = 4 := by decide
  have e45 : (a7c₂ : Perm (Fin 7)) 4 = 5 := by decide
  have e53 : (a7c₂ : Perm (Fin 7)) 5 = 3 := by decide
  have s1 := fun {y : Fin 7} (hy : y ∈ orbit H x) => a7_orbit_closed H hc₁ hy
  have s2 := fun {y : Fin 7} (hy : y ∈ orbit H x) => a7_orbit_closed H hc₂ hy
  refine ⟨⟨fun h => e01 ▸ s1 h, fun h => e20 ▸ s1 (e12 ▸ s1 h)⟩,
    ⟨fun h => e12 ▸ s1 h, fun h => e01 ▸ s1 (e20 ▸ s1 h)⟩,
    ⟨fun h => e34 ▸ s2 h, fun h => e53 ▸ s2 (e45 ▸ s2 h)⟩,
    ⟨fun h => e45 ▸ s2 h, fun h => e34 ▸ s2 (e53 ▸ s2 h)⟩⟩

@[expose] noncomputable def a7StabHom :
    alternatingGroup {x : Fin 7 // x ≠ 6} →* stabilizer (alternatingGroup (Fin 7)) (6 : Fin 7) where
  toFun τ := ⟨⟨Perm.ofSubtype (τ : Perm {x : Fin 7 // x ≠ 6}), by
      rw [Perm.mem_alternatingGroup, Perm.sign_ofSubtype]
      exact τ.2⟩, by
      rw [mem_stabilizer_iff, a7_smul_def]
      exact Perm.ofSubtype_apply_of_not_mem _ (by simp)⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_one Perm.ofSubtype
  map_mul' a b := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_mul Perm.ofSubtype _ _

theorem a7StabHom_bijective : Function.Bijective a7StabHom := by
  constructor
  · intro a b h
    have h' : Perm.ofSubtype (a : Perm {x : Fin 7 // x ≠ 6}) =
        Perm.ofSubtype (b : Perm {x : Fin 7 // x ≠ 6}) :=
      congrArg (fun g : stabilizer (alternatingGroup (Fin 7)) (6 : Fin 7) =>
        ((g : alternatingGroup (Fin 7)) : Perm (Fin 7))) h
    exact Subtype.ext (Perm.ofSubtype_injective h')
  · intro g
    have hg6 : ((g : alternatingGroup (Fin 7)) : Perm (Fin 7)) 6 = 6 := g.2
    have h₁ : ∀ x : Fin 7, ((g : alternatingGroup (Fin 7)) : Perm (Fin 7)) x ≠ 6 ↔ x ≠ 6 := by
      intro x
      constructor
      · intro hx hx6
        rw [hx6, hg6] at hx
        exact hx rfl
      · intro hx hx6
        exact hx (((g : alternatingGroup (Fin 7)) : Perm (Fin 7)).injective (hx6.trans hg6.symm))
    have h₂ : ∀ x : Fin 7, ((g : alternatingGroup (Fin 7)) : Perm (Fin 7)) x ≠ x → x ≠ 6 := by
      intro x hx hx6
      rw [hx6] at hx
      exact hx hg6
    have hsub := Perm.ofSubtype_subtypePerm h₁ h₂
    refine ⟨⟨((g : alternatingGroup (Fin 7)) : Perm (Fin 7)).subtypePerm h₁, ?_⟩, ?_⟩
    · rw [Perm.mem_alternatingGroup, ← Perm.sign_ofSubtype, hsub]
      exact (g : alternatingGroup (Fin 7)).2
    · apply Subtype.ext
      apply Subtype.ext
      exact hsub

@[expose] noncomputable def a7StabEquiv :
    alternatingGroup {x : Fin 7 // x ≠ 6} ≃* stabilizer (alternatingGroup (Fin 7)) (6 : Fin 7) :=
  MulEquiv.ofBijective a7StabHom a7StabHom_bijective

theorem a7_stab_six : IsSimpleGroup (stabilizer (alternatingGroup (Fin 7)) (6 : Fin 7)) ∧
    Nat.card (stabilizer (alternatingGroup (Fin 7)) (6 : Fin 7)) = 360 := by
  have hcard : Nat.card {x : Fin 7 // x ≠ 6} = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_fin,
      Fintype.card_unique]
  have : IsSimpleGroup (alternatingGroup {x : Fin 7 // x ≠ 6}) :=
    alternatingGroup.isSimpleGroup (by rw [hcard]; norm_num)
  have : Nontrivial {x : Fin 7 // x ≠ 6} :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  refine ⟨a7StabEquiv.symm.isSimpleGroup, ?_⟩
  rw [← Nat.card_congr a7StabEquiv.toEquiv, nat_card_alternatingGroup, hcard]
  rfl

theorem a7_not_fix_six (H : Subgroup (alternatingGroup (Fin 7))) (hH : Nat.card H = 72)
    (hfix : ∀ h ∈ H, (h : Perm (Fin 7)) 6 = 6) : False := by
  obtain ⟨hs, hc⟩ := a7_stab_six
  have hle : H ≤ stabilizer (alternatingGroup (Fin 7)) (6 : Fin 7) := fun h hh => hfix h hh
  exact card_ne_seventytwo hc (H.subgroupOf _)
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hH])

theorem a7_kernel (H : Subgroup (alternatingGroup (Fin 7))) (x : Fin 7) :
    ∃ N : Subgroup (alternatingGroup (Fin 7)), N ≤ H ∧
      (∀ n ∈ N, ∀ y ∈ orbit H x, (n : Perm (Fin 7)) y = y) ∧
      (∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) ∧
      Nat.card H ≤ (orbit H x).ncard.factorial * Nat.card N := by
  let φ := MulAction.toPermHom H (orbit H x)
  refine ⟨φ.ker.map H.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · intro m hm y hy
    obtain ⟨n, hn, rfl⟩ := hm
    have h1 : φ n = 1 := MonoidHom.mem_ker.mp hn
    have h2 := congrArg (fun σ : Perm (orbit H x) => ((σ ⟨y, hy⟩ : orbit H x) : Fin 7)) h1
    simp only [φ, MulAction.toPermHom_apply, MulAction.toPerm_apply, Perm.one_apply] at h2
    exact h2
  · intro h hh m hm
    obtain ⟨n, hn, rfl⟩ := hm
    have key := (MonoidHom.normal_ker φ).conj_mem n hn ⟨h, hh⟩
    exact ⟨_, key, rfl⟩
  · have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv] at hc
    rw [hc, ← Nat.card_congr (φ.ker.equivMapOfInjective _ H.subtype_injective).toEquiv]
    refine Nat.mul_le_mul_right _ ?_
    calc Nat.card φ.range ≤ Nat.card (Perm (orbit H x)) := Subgroup.card_le_card_group _
      _ = (orbit H x).ncard.factorial := by rw [Nat.card_perm, Nat.card_coe_set_eq]

theorem ncard_four {a b c d : Fin 7} (h : [a, b, c, d].Nodup) :
    ({a, b, c, d} : Set (Fin 7)).ncard = 4 := by
  rw [show ({a, b, c, d} : Set (Fin 7)) = ↑([a, b, c, d].toFinset) by simp,
    Set.ncard_coe_finset, List.toFinset_card_of_nodup h]
  rfl

theorem set_eq_0126 {O : Set (Fin 7)} (h0 : (0 : Fin 7) ∈ O) (h1 : (1 : Fin 7) ∈ O)
    (h2 : (2 : Fin 7) ∈ O) (h3 : (3 : Fin 7) ∉ O) (h4 : (4 : Fin 7) ∉ O) (h5 : (5 : Fin 7) ∉ O)
    (h6 : (6 : Fin 7) ∈ O) : O = {0, 1, 2, 6} := by
  ext y
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  fin_cases y <;> simp [h0, h1, h2, h3, h4, h5, h6]

theorem set_eq_3456 {O : Set (Fin 7)} (h0 : (0 : Fin 7) ∉ O) (h1 : (1 : Fin 7) ∉ O)
    (h2 : (2 : Fin 7) ∉ O) (h3 : (3 : Fin 7) ∈ O) (h4 : (4 : Fin 7) ∈ O) (h5 : (5 : Fin 7) ∈ O)
    (h6 : (6 : Fin 7) ∈ O) : O = {3, 4, 5, 6} := by
  ext y
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  fin_cases y <;> simp [h0, h1, h2, h3, h4, h5, h6]

theorem set_eq_univ {O : Set (Fin 7)} (h0 : (0 : Fin 7) ∈ O) (h1 : (1 : Fin 7) ∈ O)
    (h2 : (2 : Fin 7) ∈ O) (h3 : (3 : Fin 7) ∈ O) (h4 : (4 : Fin 7) ∈ O) (h5 : (5 : Fin 7) ∈ O)
    (h6 : (6 : Fin 7) ∈ O) : O = Set.univ := by
  ext y
  simp only [Set.mem_univ, iff_true]
  fin_cases y
  exacts [h0, h1, h2, h3, h4, h5, h6]

theorem eq_six_of_mem {O : Set (Fin 7)} (h0 : (0 : Fin 7) ∉ O) (h1 : (1 : Fin 7) ∉ O)
    (h2 : (2 : Fin 7) ∉ O) (h3 : (3 : Fin 7) ∉ O) (h4 : (4 : Fin 7) ∉ O) (h5 : (5 : Fin 7) ∉ O)
    {y : Fin 7} (hy : y ∈ O) : y = 6 := by
  fin_cases y
  · exact absurd hy h0
  · exact absurd hy h1
  · exact absurd hy h2
  · exact absurd hy h3
  · exact absurd hy h4
  · exact absurd hy h5
  · rfl

theorem mem_0126 : ∀ x : Fin 7, x ≠ 3 → x ≠ 4 → x ≠ 5 → x ∈ ({0, 1, 2, 6} : Set (Fin 7)) := by
  intro x
  fin_cases x <;> simp

theorem mem_3456 : ∀ x : Fin 7, x ≠ 0 → x ≠ 1 → x ≠ 2 → x ∈ ({3, 4, 5, 6} : Set (Fin 7)) := by
  intro x
  fin_cases x <;> simp

theorem a7_not_normalize (h c : alternatingGroup (Fin 7)) (z : Fin 7)
    (hcz : (c : Perm (Fin 7)) z ≠ z) (hhz : (h : Perm (Fin 7)) 6 = z) :
    h⁻¹ * c * h⁻¹⁻¹ ∉ a7P₀ := by
  intro hmem
  have h1 := a7P₀_fix_six hmem
  rw [inv_inv] at h1
  change ((h : Perm (Fin 7))⁻¹ * (c : Perm (Fin 7)) * (h : Perm (Fin 7))) 6 = 6 at h1
  rw [Perm.mul_apply, Perm.mul_apply, hhz, Perm.inv_eq_iff_eq, hhz] at h1
  exact hcz h1

@[expose] def A7KeyConcl (H : Subgroup (alternatingGroup (Fin 7))) : Prop :=
  (∃ N : Subgroup (alternatingGroup (Fin 7)), N ≤ H ∧ Nat.card N = 3 ∧
    ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) ∧
  ∃ h ∈ H, ∃ p ∈ a7P₀, h * p * h⁻¹ ∉ a7P₀

theorem a7_key_0126 (H : Subgroup (alternatingGroup (Fin 7))) (hH : Nat.card H = 72)
    (hO : orbit H (6 : Fin 7) = {0, 1, 2, 6}) : A7KeyConcl H := by
  obtain ⟨N, hNH, hNfix, hNnorm, hNcard⟩ := a7_kernel H 6
  rw [hO, ncard_four (by decide), hH] at hNcard
  rw [hO] at hNfix
  have hle : Nat.card N ≤ 3 := card_le_three_of_fix N (a := 3) (b := 4) (c := 5) (by decide)
    fun k hk x hx3 hx4 hx5 => hNfix k hk x (mem_0126 x hx3 hx4 hx5)
  have h3 : 3 ≤ Nat.card N := by
    norm_num [Nat.factorial] at hNcard
    omega
  refine ⟨⟨N, hNH, by omega, hNnorm⟩, ?_⟩
  have h0 : (0 : Fin 7) ∈ orbit H (6 : Fin 7) := by
    rw [hO]
    simp
  obtain ⟨h, hh⟩ := h0
  have hh' : ((h : alternatingGroup (Fin 7)) : Perm (Fin 7)) 6 = 0 := by
    rw [← a7_sub_smul]
    exact hh
  have hc0 : (a7c₁ : Perm (Fin 7)) 0 ≠ 0 := by
    rw [a7c₁_apply]
    decide
  have hc₁P : a7c₁ ∈ a7P₀ := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  exact ⟨(h : alternatingGroup (Fin 7))⁻¹, H.inv_mem h.2, a7c₁, hc₁P,
    a7_not_normalize _ _ 0 hc0 hh'⟩

theorem a7_key_3456 (H : Subgroup (alternatingGroup (Fin 7))) (hH : Nat.card H = 72)
    (hO : orbit H (6 : Fin 7) = {3, 4, 5, 6}) : A7KeyConcl H := by
  obtain ⟨N, hNH, hNfix, hNnorm, hNcard⟩ := a7_kernel H 6
  rw [hO, ncard_four (by decide), hH] at hNcard
  rw [hO] at hNfix
  have hle : Nat.card N ≤ 3 := card_le_three_of_fix N (a := 0) (b := 1) (c := 2) (by decide)
    fun k hk x hx0 hx1 hx2 => hNfix k hk x (mem_3456 x hx0 hx1 hx2)
  have h3 : 3 ≤ Nat.card N := by
    norm_num [Nat.factorial] at hNcard
    omega
  refine ⟨⟨N, hNH, by omega, hNnorm⟩, ?_⟩
  have h3' : (3 : Fin 7) ∈ orbit H (6 : Fin 7) := by
    rw [hO]
    simp
  obtain ⟨h, hh⟩ := h3'
  have hh' : ((h : alternatingGroup (Fin 7)) : Perm (Fin 7)) 6 = 3 := by
    rw [← a7_sub_smul]
    exact hh
  have hc3 : (a7c₂ : Perm (Fin 7)) 3 ≠ 3 := by
    rw [a7c₂_apply]
    decide
  have hc₂P : a7c₂ ∈ a7P₀ := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  exact ⟨(h : alternatingGroup (Fin 7))⁻¹, H.inv_mem h.2, a7c₂, hc₂P,
    a7_not_normalize _ _ 3 hc3 hh'⟩

theorem a7_key (H : Subgroup (alternatingGroup (Fin 7))) (hc₁ : a7c₁ ∈ H) (hc₂ : a7c₂ ∈ H)
    (hH : Nat.card H = 72) : A7KeyConcl H := by
  obtain ⟨i01, i12, i34, i45⟩ := a7_orbit_iff H hc₁ hc₂ 6
  have h6 : (6 : Fin 7) ∈ orbit H (6 : Fin 7) := mem_orbit_self _
  by_cases h0 : (0 : Fin 7) ∈ orbit H (6 : Fin 7) <;>
    by_cases h3 : (3 : Fin 7) ∈ orbit H (6 : Fin 7)
  · exfalso
    have hdvd : (orbit H (6 : Fin 7)).ncard ∣ 72 := by
      rw [← hH, ← index_stabilizer]
      exact Subgroup.index_dvd_card _
    rw [set_eq_univ h0 (i01.1 h0) (i12.1 (i01.1 h0)) h3 (i34.1 h3) (i45.1 (i34.1 h3)) h6,
      Set.ncard_univ, Nat.card_fin] at hdvd
    norm_num at hdvd
  · exact a7_key_0126 H hH (set_eq_0126 h0 (i01.1 h0) (i12.1 (i01.1 h0)) h3
      (fun h => h3 (i34.2 h)) (fun h => h3 (i34.2 (i45.2 h))) h6)
  · exact a7_key_3456 H hH (set_eq_3456 h0 (fun h => h0 (i01.2 h))
      (fun h => h0 (i01.2 (i12.2 h))) h3 (i34.1 h3) (i45.1 (i34.1 h3)) h6)
  · exfalso
    refine a7_not_fix_six H hH fun h hh => ?_
    exact eq_six_of_mem h0 (fun h => h0 (i01.2 h)) (fun h => h0 (i01.2 (i12.2 h))) h3
      (fun h => h3 (i34.2 h)) (fun h => h3 (i34.2 (i45.2 h))) (a7_orbit_closed H hh h6)

end CFSG.Quasithin.F134
