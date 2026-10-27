module

public import CFSG.LieType.Chevalley.RootDiagonalTorusWords
public import CFSG.RankThree.CentralCover.SteinbergBNCoverPairingCore
public import CFSG.LieType.Chevalley.RootCommutatorReduction

public section

namespace CFSG.RankThree.PartOne

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

@[expose] def oddF4SixRoots : Fin 6 → Fin Tag.F4.rank → ℤ :=
  ![![2, 3, 4, 2], ![1, 3, 4, 2], ![1, 2, 4, 2], ![1, 2, 2, 0], ![1, 1, 2, 0], ![0, 1, 2, 0]]

theorem oddF4SixRoots_isRoot (i : Fin 6) : IsRoot Tag.F4 (oddF4SixRoots i) :=
  RootOps.isRootB_iff.1
    ((by decide +kernel : ∀ i, RootOps.isRootB Tag.F4 (oddF4SixRoots i) = true) i)

theorem oddF4SixRoots_height_pos (i : Fin 6) : 0 < height (τ := Tag.F4) (oddF4SixRoots i) :=
  (by decide +kernel : ∀ i, 0 < height (τ := Tag.F4) (oddF4SixRoots i)) i

theorem oddF4SixRoots_injective : Function.Injective oddF4SixRoots := by decide +kernel

theorem oddF4SixRoots_iform_self (i : Fin 6) :
    iform (τ := Tag.F4) (oddF4SixRoots i) (oddF4SixRoots i) = 4 :=
  (by decide +kernel : ∀ i, iform (τ := Tag.F4) (oddF4SixRoots i) (oddF4SixRoots i) = 4) i

theorem oddF4SixRoots_iform_nonneg (i j : Fin 6) :
    0 ≤ iform (τ := Tag.F4) (oddF4SixRoots i) (oddF4SixRoots j) :=
  (by decide +kernel : ∀ i j, 0 ≤ iform (τ := Tag.F4) (oddF4SixRoots i) (oddF4SixRoots j)) i j

theorem oddF4_not_isRoot_nsmul_add_nsmul {α β : Fin Tag.F4.rank → ℤ} (hα : 3 ≤ iform α α)
    (hβ : 3 ≤ iform β β) (hαβ : 0 ≤ iform α β) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ¬ IsRoot Tag.F4 (a • α + b • β) := by
  intro h
  have h4 : iform (a • α + b • β) (a • α + b • β) ≤ 4 := by
    rcases iform_self_cases noG2_F4 h with h2 | h2 <;> omega
  rw [iform_nsmul_add_nsmul] at h4
  have hA : (1 : ℤ) ≤ (a : ℤ) ^ 2 := by
    have : (1 : ℤ) ≤ a := by exact_mod_cast ha
    nlinarith
  have hB : (1 : ℤ) ≤ (b : ℤ) ^ 2 := by
    have : (1 : ℤ) ≤ b := by exact_mod_cast hb
    nlinarith
  have hab : (0 : ℤ) ≤ 2 * a * b * iform α β := by positivity
  nlinarith [mul_le_mul hA hα (by norm_num) (by positivity),
    mul_le_mul hB hβ (by norm_num) (by positivity)]

theorem oddF4SixRoots_not_isRoot {i j : Fin 6} {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ¬ IsRoot Tag.F4 (a • oddF4SixRoots i + b • oddF4SixRoots j) :=
  oddF4_not_isRoot_nsmul_add_nsmul (by rw [oddF4SixRoots_iform_self]; norm_num)
    (by rw [oddF4SixRoots_iform_self]; norm_num) (oddF4SixRoots_iform_nonneg i j) ha hb

section Span

variable (K : Type) [Field K]

theorem oddF4SixRoots_rootSubgroup_comm (i j : Fin 6)
    {x y : (Module.End K (RootModule Tag.F4 K))ˣ}
    (hx : x ∈ rootSubgroup Tag.F4 K (oddF4SixRoots i))
    (hy : y ∈ rootSubgroup Tag.F4 K (oddF4SixRoots j)) : x * y = y * x := by
  by_cases hij : i = j
  · subst hij
    exact rootSubgroup_mul_comm K hx hy
  · have hle := commutator_rootSubgroup_le K (oddF4SixRoots_isRoot i) (oddF4SixRoots_isRoot j)
      (oddF4SixRoots_height_pos i) (oddF4SixRoots_height_pos j)
      (fun h => hij (oddF4SixRoots_injective h))
    have hbot : (⨆ (γ : Fin Tag.F4.rank → ℤ) (_ : IsRoot Tag.F4 γ ∧ ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧
        γ = a • oddF4SixRoots i + b • oddF4SixRoots j), rootSubgroup Tag.F4 K γ) = ⊥ := by
      refine iSup_eq_bot.mpr fun γ => iSup_eq_bot.mpr fun ⟨hγ, a, b, ha, hb, hγe⟩ => ?_
      exact absurd (hγe ▸ hγ) (oddF4SixRoots_not_isRoot ha hb)
    have := hle (Subgroup.commutator_mem_commutator hx hy)
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this

@[expose] def oddF4SixGens : Set (Module.End K (RootModule Tag.F4 K))ˣ :=
  ⋃ i : Fin 6, Set.range (pinnedX Tag.F4 K (oddF4SixRoots i))

@[expose] noncomputable def oddF4SixU : Subgroup (Module.End K (RootModule Tag.F4 K))ˣ :=
  rootSpan Tag.F4 K (Set.range oddF4SixRoots)

theorem oddF4SixU_eq_closure : oddF4SixU K = Subgroup.closure (oddF4SixGens K) := by
  rw [oddF4SixU, rootSpan, iSup_range]
  simp only [rootSubgroup, oddF4SixGens, Subgroup.closure_iUnion]

theorem oddF4SixGens_comm {s t : (Module.End K (RootModule Tag.F4 K))ˣ}
    (hs : s ∈ oddF4SixGens K) (ht : t ∈ oddF4SixGens K) : Commute s t := by
  simp only [oddF4SixGens, Set.mem_iUnion, Set.mem_range] at hs ht
  obtain ⟨i, c, rfl⟩ := hs
  obtain ⟨j, d, rfl⟩ := ht
  exact oddF4SixRoots_rootSubgroup_comm K i j (mem_rootSubgroup.2 ⟨c, rfl⟩)
    (mem_rootSubgroup.2 ⟨d, rfl⟩)

theorem oddF4SixU_comm {x y : (Module.End K (RootModule Tag.F4 K))ˣ} (hx : x ∈ oddF4SixU K)
    (hy : y ∈ oddF4SixU K) : x * y = y * x := by
  rw [oddF4SixU_eq_closure] at hx hy
  exact (CFSG.RankThree.CentralCover.commute_of_mem_closure
    (fun s hs t ht => oddF4SixGens_comm K hs ht) hx hy).eq

theorem oddF4SixU_pow {p : ℕ} [Fact p.Prime] [CharP K p]
    {x : (Module.End K (RootModule Tag.F4 K))ˣ} (hx : x ∈ oddF4SixU K) : x ^ p = 1 := by
  rw [oddF4SixU_eq_closure] at hx
  refine CFSG.RankThree.CentralCover.pow_eq_one_of_mem_closure
    (fun s hs t ht => oddF4SixGens_comm K hs ht) (fun s hs => ?_) hx
  simp only [oddF4SixGens, Set.mem_iUnion, Set.mem_range] at hs
  obtain ⟨i, c, rfl⟩ := hs
  by_cases h1 : pinnedX Tag.F4 K (oddF4SixRoots i) c = 1
  · rw [h1, one_pow]
  · have := orderOf_eq_of_mem_rootSubgroup (p := p) (mem_rootSubgroup.2 ⟨c, rfl⟩) h1
    rw [← this, pow_orderOf_eq_one]

theorem oddF4SixU_le_adjointGroup : oddF4SixU K ≤ adjointGroup Tag.F4 K :=
  iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α

theorem oddF4SixU_card : Nat.card (oddF4SixU K) = Nat.card K ^ 6 := by
  have hS : ∀ α ∈ Set.range oddF4SixRoots, IsRoot Tag.F4 α ∧ 0 < height α := by
    rintro _ ⟨i, rfl⟩
    exact ⟨oddF4SixRoots_isRoot i, oddF4SixRoots_height_pos i⟩
  have hclosed : ∀ α ∈ Set.range oddF4SixRoots, ∀ β ∈ Set.range oddF4SixRoots, ∀ a b : ℕ,
      1 ≤ a → 1 ≤ b → IsRoot Tag.F4 (a • α + b • β) →
        a • α + b • β ∈ Set.range oddF4SixRoots := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ a b ha hb h
    exact absurd h (oddF4SixRoots_not_isRoot ha hb)
  have hbij := (positive_root_collection Tag.F4 K).1 _ hS hclosed oddF4SixRoots
    oddF4SixRoots_injective rfl
  have e := hbij.equiv _
  rw [oddF4SixU]
  calc Nat.card (rootSpan Tag.F4 K (Set.range oddF4SixRoots))
      = Nat.card (Set.univ : Set (Fin 6 → K)) := (Nat.card_congr e).symm
    _ = Nat.card K ^ 6 := by
      rw [Nat.card_univ, Nat.card_pi]
      simp

end Span

section Torus

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def oddF4SixIdx : Fin Tag.F4.rank := ⟨2, by decide⟩

variable (K : Type) [Field K]

@[expose] def oddF4SixSign : Fin Tag.F4.rank → Kˣ := fun i => if i = oddF4SixIdx then -1 else 1

theorem oddF4SixSign_mul_self : oddF4SixSign K * oddF4SixSign K = 1 := by
  funext i
  by_cases hi : i = oddF4SixIdx <;> simp [oddF4SixSign, hi]

theorem oddF4SixSign_rootChar_eq (v : Fin Tag.F4.rank → ℤ) :
    rootChar (oddF4SixSign K) v = (-1) ^ v oddF4SixIdx := by
  rw [rootChar, Finset.prod_eq_single oddF4SixIdx]
  · simp [oddF4SixSign]
  · intro i _ hi
    simp [oddF4SixSign, hi]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem oddF4SixSign_rootChar (i : Fin 6) :
    rootChar (oddF4SixSign K) (oddF4SixRoots i) = 1 := by
  rw [oddF4SixSign_rootChar_eq]
  have : Even (oddF4SixRoots i oddF4SixIdx) :=
    (by decide +kernel : ∀ i : Fin 6, Even (oddF4SixRoots i oddF4SixIdx)) i
  exact this.neg_one_zpow

theorem oddF4SixSign_mem : rootDiagUnit Tag.F4 (oddF4SixSign K) ∈ adjointGroup Tag.F4 K := by
  obtain ⟨⟨B, hB, -⟩, hrest⟩ := G2_F4_root_character_diagonals_inner Tag.F4 (Or.inr rfl) K
  obtain ⟨-, -, h, -⟩ := hrest B hB (oddF4SixSign K)
  exact h

@[expose] noncomputable def oddF4SixTorus : adjointGroup Tag.F4 K :=
  ⟨rootDiagUnit Tag.F4 (oddF4SixSign K), oddF4SixSign_mem K⟩

theorem oddF4SixTorus_mul_self : oddF4SixTorus K * oddF4SixTorus K = 1 :=
  Subtype.ext (by
    change rootDiagUnit Tag.F4 (oddF4SixSign K) * rootDiagUnit Tag.F4 (oddF4SixSign K) = 1
    rw [← rootDiagUnit_mul, oddF4SixSign_mul_self, rootDiagUnit_one])

theorem oddF4SixTorus_ne_one (h2 : (2 : K) ≠ 0) : oddF4SixTorus K ≠ 1 := by
  intro h
  have h1 : rootDiagUnit Tag.F4 (oddF4SixSign K) = 1 := congrArg Subtype.val h
  have h3 : rootDiag (oddF4SixSign K) = (1 : Module.End K (RootModule Tag.F4 K)) :=
    congrArg Units.val h1
  let b : Label Tag.F4 := Sum.inr ⟨Pi.single oddF4SixIdx 1, isRoot_single Tag.F4 oddF4SixIdx⟩
  have h4 := congrArg (fun f : Module.End K (RootModule Tag.F4 K) => f (Finsupp.single b 1)) h3
  simp only [Module.End.one_apply] at h4
  rw [rootDiag_single] at h4
  have h5 := congrArg (fun x : RootModule Tag.F4 K => x b) h4
  simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at h5
  have h6 : rootChar (oddF4SixSign K) (labelWt Tag.F4 b) = -1 := by
    rw [oddF4SixSign_rootChar_eq]
    change (-1 : Kˣ) ^ (Pi.single oddF4SixIdx (1 : ℤ) : Fin Tag.F4.rank → ℤ) oddF4SixIdx = -1
    simp
  rw [h6] at h5
  apply h2
  have : ((-1 : Kˣ) : K) = 1 := h5
  simp only [Units.val_neg, Units.val_one] at this
  linear_combination -this

theorem oddF4SixTorus_comm {x : adjointGroup Tag.F4 K}
    (hx : (x : ModGL Tag.F4 K) ∈ oddF4SixU K) : oddF4SixTorus K * x = x * oddF4SixTorus K := by
  rw [oddF4SixU_eq_closure] at hx
  have hgen : ∀ g ∈ oddF4SixGens K, rootDiagUnit Tag.F4 (oddF4SixSign K) * g =
      g * rootDiagUnit Tag.F4 (oddF4SixSign K) := by
    intro g hg
    simp only [oddF4SixGens, Set.mem_iUnion, Set.mem_range] at hg
    obtain ⟨i, c, rfl⟩ := hg
    have := rootDiagUnit_conj_pinnedX (K := K) (oddF4SixSign K) (oddF4SixRoots_isRoot i) c
    rw [oddF4SixSign_rootChar, Units.val_one, one_mul] at this
    exact mul_inv_eq_iff_eq_mul.mp this
  have hle : Subgroup.closure (oddF4SixGens K) ≤
      Subgroup.centralizer {rootDiagUnit Tag.F4 (oddF4SixSign K)} :=
    (Subgroup.closure_le _).2 fun g hg =>
      Subgroup.mem_centralizer_singleton_iff.2 (hgen g hg).symm
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hle hx)).symm

end Torus

section Assembly

variable (K : Type) [Field K]

@[expose] noncomputable def oddF4SixUC : Subgroup (adjointGroup Tag.F4 K) :=
  (oddF4SixU K).subgroupOf (adjointGroup Tag.F4 K)

theorem oddF4SixUC_card : Nat.card (oddF4SixUC K) = Nat.card K ^ 6 := by
  rw [oddF4SixUC, Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe (oddF4SixU_le_adjointGroup K)).toEquiv, oddF4SixU_card]

theorem oddF4SixUC_isElementaryAbelian {p : ℕ} [Fact p.Prime] [CharP K p] :
    IsElementaryAbelian p (oddF4SixUC K) := by
  refine
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩
      exponent_dvd_p := ?_ }
  · exact oddF4SixU_comm K (Subgroup.mem_subgroupOf.1 a.2) (Subgroup.mem_subgroupOf.1 b.2)
  · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (Subtype.ext ?_)
    exact oddF4SixU_pow K (Subgroup.mem_subgroupOf.1 x.2)

theorem oddF4SixUC_comm_torus (h2 : (2 : K) ≠ 0) :
    orderOf (oddF4SixTorus K) = 2 ∧ ∀ x ∈ oddF4SixUC K, Commute (oddF4SixTorus K) x :=
  ⟨orderOf_eq_prime (by rw [pow_two]; exact oddF4SixTorus_mul_self K)
      (oddF4SixTorus_ne_one K h2),
    fun x hx => oddF4SixTorus_comm K (Subgroup.mem_subgroupOf.1 hx)⟩

end Assembly

end CFSG.RankThree.PartOne
