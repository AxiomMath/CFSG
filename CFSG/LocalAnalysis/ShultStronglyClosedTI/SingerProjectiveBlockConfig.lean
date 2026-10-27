module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SingerProjectiveGeometry
public import Mathlib.FieldTheory.Finite.Basic

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.Singer

open scoped LinearAlgebra.Projectivization Pointwise
open Projectivization Module

section ncard

variable {ι α : Type*}

theorem ncard_biUnion_le (s : Finset ι) (t : ι → Set α) :
    (⋃ i ∈ s, t i).ncard ≤ ∑ i ∈ s, (t i).ncard := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left ih _)

theorem ncard_biUnion_of_pairwiseDisjoint [Finite α] (s : Finset ι) (t : ι → Set α)
    (h : (s : Set ι).PairwiseDisjoint t) :
    (⋃ i ∈ s, t i).ncard = ∑ i ∈ s, (t i).ncard := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha, Set.ncard_union_eq,
      ih (h.subset (by simp))]
    rw [Set.disjoint_iUnion₂_right]
    intro i hi
    exact h (by simp) (by simp [hi]) (by rintro rfl; exact ha hi)

end ncard

variable (k V : Type*) [Field k] [AddCommGroup V] [Module k V]

structure BlockConfig where
  P : Set (Set (ℙ k V))
  K : Subgroup (V ≃ₗ[k] V)
  δ : ℕ
  existsUnique : ∀ p : ℙ k V, ∃! Δ, Δ ∈ P ∧ p ∈ Δ
  ncard_eq : ∀ Δ ∈ P, Δ.ncard = δ
  one_lt : 1 < δ
  exists_ne : ∃ Δ ∈ P, ∃ Γ ∈ P, Δ ≠ Γ
  transitive : ∀ Δ ∈ P, ∀ Γ ∈ P, ∃ g : V ≃ₗ[k] V, g • Δ = Γ
  smul_eq : ∀ h ∈ K, ∀ Δ ∈ P, h • Δ = Δ
  twoTransitive : ∀ Δ ∈ P, ∀ x ∈ Δ, ∀ y ∈ Δ, ∀ x' ∈ Δ, ∀ y' ∈ Δ, x ≠ y → x' ≠ y' →
    ∃ h ∈ K, h • x = x' ∧ h • y = y'
  spans : ∀ Δ ∈ P, ⨆ p ∈ Δ, p.submodule = ⊤

namespace BlockConfig

variable {k V} (C : BlockConfig k V)

theorem eq_of_mem {Δ Γ : Set (ℙ k V)} (hΔ : Δ ∈ C.P) (hΓ : Γ ∈ C.P) {p : ℙ k V} (hpΔ : p ∈ Δ)
    (hpΓ : p ∈ Γ) : Δ = Γ :=
  (C.existsUnique p).unique ⟨hΔ, hpΔ⟩ ⟨hΓ, hpΓ⟩

theorem notMem_of_ne {Δ Γ : Set (ℙ k V)} (hΔ : Δ ∈ C.P) (hΓ : Γ ∈ C.P) (hne : Γ ≠ Δ)
    {p : ℙ k V} (hp : p ∈ Δ) : p ∉ Γ :=
  fun h => hne (C.eq_of_mem hΓ hΔ h hp)

theorem smul_mem_iff {h : V ≃ₗ[k] V} (hh : h ∈ C.K) {Δ : Set (ℙ k V)} (hΔ : Δ ∈ C.P)
    {p : ℙ k V} : h • p ∈ Δ ↔ p ∈ Δ := by
  conv_lhs => rw [← C.smul_eq h hh Δ hΔ]
  exact Set.smul_mem_smul_set_iff

theorem exists_block : ∃ Δ, Δ ∈ C.P := by
  obtain ⟨Δ, hΔ, -⟩ := C.exists_ne
  exact ⟨Δ, hΔ⟩

theorem exists_pair [Finite V] {Δ : Set (ℙ k V)} (hΔ : Δ ∈ C.P) : ∃ x ∈ Δ, ∃ y ∈ Δ, x ≠ y := by
  have h := C.ncard_eq Δ hΔ
  obtain ⟨x, y, hx, hy, hxy⟩ := (Set.one_lt_ncard_iff (Set.toFinite Δ)).mp (h ▸ C.one_lt)
  exact ⟨x, hx, y, hy, hxy⟩

theorem nonempty [Finite V] {Δ : Set (ℙ k V)} (hΔ : Δ ∈ C.P) : Δ.Nonempty := by
  obtain ⟨x, hx, -⟩ := C.exists_pair hΔ
  exact ⟨x, hx⟩

theorem ncard_secant_eq {Δ Γ : Set (ℙ k V)} (hΔ : Δ ∈ C.P) (hΓ : Γ ∈ C.P) {x y x' y' : ℙ k V}
    (hx : x ∈ Δ) (hy : y ∈ Δ) (hxy : x ≠ y) (hx' : x' ∈ Γ) (hy' : y' ∈ Γ) (hxy' : x' ≠ y') :
    (pointsIn (line x y) ∩ Δ).ncard = (pointsIn (line x' y') ∩ Γ).ncard := by
  obtain ⟨g, hg⟩ := C.transitive Δ hΔ Γ hΓ
  have hgx : g • x ∈ Γ := hg ▸ Set.smul_mem_smul_set hx
  have hgy : g • y ∈ Γ := hg ▸ Set.smul_mem_smul_set hy
  obtain ⟨h, hK, hhx, hhy⟩ := C.twoTransitive Γ hΓ _ hgx _ hgy x' hx' y' hy'
    (fun e => hxy (MulAction.injective g e)) hxy'
  rw [← Set.ncard_smul_set (h * g), Set.smul_set_inter, smul_pointsIn_line, mul_smul, mul_smul,
    hhx, hhy, mul_smul, hg, C.smul_eq h hK Γ hΓ]

theorem exists_ncard_secant [Finite V] : ∃ l : ℕ, ∀ Δ ∈ C.P, ∀ x ∈ Δ, ∀ y ∈ Δ, x ≠ y →
    (pointsIn (line x y) ∩ Δ).ncard = l := by
  obtain ⟨Δ₀, hΔ₀⟩ := C.exists_block
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy₀⟩ := C.exists_pair hΔ₀
  exact ⟨_, fun Δ hΔ x hx y hy hxy => C.ncard_secant_eq hΔ hΔ₀ hx hy hxy hx₀ hy₀ hxy₀⟩

def l [Finite V] : ℕ := Classical.choose C.exists_ncard_secant

theorem ncard_secant [Finite V] {Δ : Set (ℙ k V)} (hΔ : Δ ∈ C.P) {x y : ℙ k V} (hx : x ∈ Δ) (hy : y ∈ Δ)
    (hxy : x ≠ y) : (pointsIn (line x y) ∩ Δ).ncard = C.l :=
  Classical.choose_spec C.exists_ncard_secant Δ hΔ x hx y hy hxy

theorem not_pointsIn_line_subset [Finite k] [Finite V] {Δ : Set (ℙ k V)} (hΔ : Δ ∈ C.P) {x y : ℙ k V} (hx : x ∈ Δ)
    (hy : y ∈ Δ) (hxy : x ≠ y) : ¬ pointsIn (line x y) ⊆ Δ := by
  intro hsub
  have hall : ∀ x' ∈ Δ, ∀ y' ∈ Δ, x' ≠ y' → pointsIn (line x' y') ⊆ Δ := by
    intro x' hx' y' hy' hxy'
    have h1 : (pointsIn (line x' y') ∩ Δ).ncard = (pointsIn (line x' y')).ncard := by
      rw [C.ncard_secant hΔ hx' hy' hxy', ← C.ncard_secant hΔ hx hy hxy,
        Set.inter_eq_left.mpr hsub, ncard_pointsIn_line hxy, ncard_pointsIn_line hxy']
    exact Set.inter_eq_left.mp (Set.eq_of_subset_of_ncard_le Set.inter_subset_left h1.ge)
  let U : Submodule k V :=
    { carrier := {v | ∀ hv : v ≠ 0, Projectivization.mk k v hv ∈ Δ}
      add_mem' := by
        intro v w hv hw hvw
        by_cases hv0 : v = 0
        · subst hv0
          simp only [zero_add] at hvw ⊢
          exact hw hvw
        by_cases hw0 : w = 0
        · subst hw0
          simp only [add_zero] at hvw ⊢
          exact hv hvw
        have hmem : Projectivization.mk k (v + w) hvw ∈ pointsIn (line (Projectivization.mk k v hv0) (Projectivization.mk k w hw0)) := by
          rw [mk_mem_pointsIn, line_def, submodule_mk, submodule_mk]
          exact Submodule.add_mem_sup (Submodule.mem_span_singleton_self v)
            (Submodule.mem_span_singleton_self w)
        by_cases he : Projectivization.mk k v hv0 = Projectivization.mk k w hw0
        · rw [he, line_def, sup_idem] at hmem
          rw [eq_of_mem_pointsIn_submodule hmem]
          exact hw hw0
        · exact hall _ (hv hv0) _ (hw hw0) he hmem
      zero_mem' := fun h => absurd rfl h
      smul_mem' := by
        intro c v hv hcv
        have hv0 : v ≠ 0 := right_ne_zero_of_smul hcv
        have : Projectivization.mk k (c • v) hcv = Projectivization.mk k v hv0 := (mk_eq_mk_iff' k _ _ hcv hv0).mpr ⟨c, rfl⟩
        rw [this]
        exact hv hv0 }
  have hU : (⊤ : Submodule k V) ≤ U := by
    rw [← C.spans Δ hΔ]
    refine iSup₂_le fun p hp => ?_
    rw [submodule_eq, Submodule.span_singleton_le_iff_mem]
    intro h
    rw [mk_rep]
    exact hp
  have hevery : ∀ q : ℙ k V, q ∈ Δ := fun q => by
    have h := hU (Submodule.mem_top : q.rep ∈ ⊤)
    have h' : Projectivization.mk k q.rep q.rep_nonzero ∈ Δ := h q.rep_nonzero
    rwa [mk_rep] at h'
  obtain ⟨Δ', hΔ', Γ', hΓ', hne⟩ := C.exists_ne
  obtain ⟨q, hq⟩ := C.nonempty hΔ'
  obtain ⟨q', hq'⟩ := C.nonempty hΓ'
  exact hne ((C.eq_of_mem hΔ' hΔ hq (hevery q)).trans (C.eq_of_mem hΔ hΓ' (hevery q') hq'))

theorem exists_notMem_secant [Finite k] [Finite V] {Δ : Set (ℙ k V)} (hΔ : Δ ∈ C.P) {x y : ℙ k V} (hx : x ∈ Δ)
    (hy : y ∈ Δ) (hxy : x ≠ y) : ∃ o ∈ pointsIn (line x y), o ∉ Δ := by
  by_contra h
  push Not at h
  exact C.not_pointsIn_line_subset hΔ hx hy hxy h

theorem not_subset_pointsIn [FiniteDimensional k V] {Δ : Set (ℙ k V)} (hΔ : Δ ∈ C.P)
    {W : Submodule k V} (hW : finrank k W < finrank k V) : ¬ Δ ⊆ pointsIn W := by
  intro hsub
  have htop : (⊤ : Submodule k V) ≤ W := by
    rw [← C.spans Δ hΔ]
    exact iSup₂_le fun p hp => hsub hp
  have := Submodule.finrank_mono htop
  rw [finrank_top] at this
  omega

theorem exists_notMem_line [FiniteDimensional k V] (hn : 3 ≤ finrank k V)
    {Δ : Set (ℙ k V)} (hΔ : Δ ∈ C.P) (x y : ℙ k V) : ∃ z ∈ Δ, z ∉ pointsIn (line x y) := by
  by_contra h
  push Not at h
  exact C.not_subset_pointsIn hΔ ((finrank_line_le x y).trans_lt (by omega)) h

theorem l_lt [Finite V] [FiniteDimensional k V] (hn : 3 ≤ finrank k V) : C.l < C.δ := by
  obtain ⟨Δ, hΔ⟩ := C.exists_block
  obtain ⟨x, hx, y, hy, hxy⟩ := C.exists_pair hΔ
  rw [← C.ncard_secant hΔ hx hy hxy, ← C.ncard_eq Δ hΔ]
  refine Set.ncard_lt_ncard ⟨Set.inter_subset_right, fun hsub => ?_⟩
  obtain ⟨z, hz, hz'⟩ := C.exists_notMem_line hn hΔ x y
  exact hz' (hsub hz).1

theorem one_le_l [Finite V] : 1 ≤ C.l := by
  obtain ⟨Δ, hΔ⟩ := C.exists_block
  obtain ⟨x, hx, y, hy, hxy⟩ := C.exists_pair hΔ
  rw [← C.ncard_secant hΔ hx hy hxy]
  exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨x, left_mem_pointsIn_line x y, hx⟩

theorem ncard_inter_le_one [Finite V] [FiniteDimensional k V] (hn : 3 ≤ finrank k V)
    {Δ Γ : Set (ℙ k V)} (hΔ : Δ ∈ C.P) (hΓ : Γ ∈ C.P) (hΓΔ : Γ ≠ Δ) {x y : ℙ k V} (hx : x ∈ Δ)
    (hy : y ∈ Δ) (hxy : x ≠ y) : (pointsIn (line x y) ∩ Γ).ncard ≤ 1 := by
  classical
  by_contra hlt
  push Not at hlt
  obtain ⟨u, w, hu, hw, huw⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp hlt
  have hline : line u w = line x y := line_eq_line_of_mem hxy huw hu.1 hw.1
  have hΓl : (pointsIn (line x y) ∩ Γ).ncard = C.l := by
    rw [← hline]
    exact C.ncard_secant hΓ hu.2 hw.2 huw
  have hxΓ : x ∉ Γ := C.notMem_of_ne hΔ hΓ hΓΔ hx
  have hfin : (Δ \ {x}).Finite := Set.toFinite _
  set M := hfin.toFinset.image (fun z => line x z) with hM
  have hmemM : ∀ L ∈ M, ∃ z ∈ Δ, z ≠ x ∧ L = line x z := by
    intro L hL
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hL
    rw [Set.Finite.mem_toFinset] at hz
    exact ⟨z, hz.1, hz.2, rfl⟩
  have hMΓ : ∀ L ∈ M, (pointsIn L ∩ Γ).ncard = C.l := by
    intro L hL
    obtain ⟨z, hz, hzx, rfl⟩ := hmemM L hL
    obtain ⟨h, hK, hhx, hhy⟩ := C.twoTransitive Δ hΔ x hx y hy x hx z hz hxy (Ne.symm hzx)
    have hc := Set.ncard_smul_set h (pointsIn (line x y) ∩ Γ)
    rw [Set.smul_set_inter, smul_pointsIn_line, hhx, hhy, C.smul_eq h hK Γ hΓ] at hc
    rw [hc, hΓl]
  have hMΔ : ∀ L ∈ M, ((pointsIn L ∩ Δ) \ {x}).ncard = C.l - 1 := by
    intro L hL
    obtain ⟨z, hz, hzx, rfl⟩ := hmemM L hL
    rw [Set.ncard_sdiff_singleton_of_mem
      (show x ∈ pointsIn (line x z) ∩ Δ from ⟨left_mem_pointsIn_line x z, hx⟩),
      C.ncard_secant hΔ hx hz (Ne.symm hzx)]
  have h1 : C.δ - 1 ≤ M.card * (C.l - 1) := by
    have hsub : Δ \ {x} ⊆ ⋃ L ∈ M, (pointsIn L ∩ Δ) \ {x} := by
      intro z hz
      refine Set.mem_iUnion₂.mpr ⟨line x z, Finset.mem_image_of_mem _ ?_,
        ⟨right_mem_pointsIn_line x z, hz.1⟩, hz.2⟩
      rwa [Set.Finite.mem_toFinset]
    calc C.δ - 1 = (Δ \ {x}).ncard := by rw [Set.ncard_sdiff_singleton_of_mem hx, C.ncard_eq Δ hΔ]
      _ ≤ (⋃ L ∈ M, (pointsIn L ∩ Δ) \ {x}).ncard := Set.ncard_le_ncard hsub
      _ ≤ ∑ L ∈ M, ((pointsIn L ∩ Δ) \ {x}).ncard := ncard_biUnion_le _ _
      _ = M.card * (C.l - 1) := by rw [Finset.sum_congr rfl hMΔ, Finset.sum_const, smul_eq_mul]
  have h2 : M.card * C.l ≤ C.δ := by
    have hdisj : (M : Set (Submodule k V)).PairwiseDisjoint (fun L => pointsIn L ∩ Γ) := by
      intro L hL L' hL' hne
      rw [Function.onFun, Set.disjoint_left]
      rintro r ⟨hrL, hrΓ⟩ ⟨hrL', -⟩
      obtain ⟨z, -, hzx, rfl⟩ := hmemM L hL
      obtain ⟨z', -, hzx', rfl⟩ := hmemM L' hL'
      have hrx : r ≠ x := fun e => hxΓ (e ▸ hrΓ)
      exact hne ((line_eq_of_mem (Ne.symm hzx) hrL hrx).symm.trans
        (line_eq_of_mem (Ne.symm hzx') hrL' hrx))
    calc M.card * C.l = ∑ L ∈ M, (pointsIn L ∩ Γ).ncard := by
          rw [Finset.sum_congr rfl hMΓ, Finset.sum_const, smul_eq_mul]
      _ = (⋃ L ∈ M, pointsIn L ∩ Γ).ncard := (ncard_biUnion_of_pairwiseDisjoint _ _ hdisj).symm
      _ ≤ Γ.ncard := Set.ncard_le_ncard (Set.iUnion₂_subset fun L _ => Set.inter_subset_right)
      _ = C.δ := C.ncard_eq Γ hΓ
  have hl := C.l_lt hn
  have hδ := C.one_lt
  have hl1 := C.one_le_l
  have key : M.card * (C.l - 1) + M.card = M.card * C.l := by
    rw [← Nat.mul_add_one, Nat.sub_add_cancel hl1]
  rcases Nat.lt_or_ge M.card 2 with hc | hc
  · interval_cases h : M.card <;> omega
  · omega

theorem smul_eq_self_of_notMem [Finite V] [FiniteDimensional k V] (hn : 3 ≤ finrank k V)
    {Δ : Set (ℙ k V)} (hΔ : Δ ∈ C.P) {x y : ℙ k V} (hx : x ∈ Δ) (hy : y ∈ Δ) (hxy : x ≠ y)
    {h : V ≃ₗ[k] V} (hK : h ∈ C.K) (hL : line (h • x) (h • y) = line x y) {o : ℙ k V}
    (ho : o ∈ pointsIn (line x y)) (hoΔ : o ∉ Δ) : h • o = o := by
  obtain ⟨Γ, ⟨hΓ, hoΓ⟩, -⟩ := C.existsUnique o
  have hΓΔ : Γ ≠ Δ := fun e => hoΔ (e ▸ hoΓ)
  have h1 : h • o ∈ pointsIn (line x y) ∩ Γ :=
    ⟨hL ▸ smul_mem_pointsIn_line_iff.mpr ho, (C.smul_mem_iff hK hΓ).mpr hoΓ⟩
  exact (Set.ncard_le_one (Set.toFinite _)).mp (C.ncard_inter_le_one hn hΔ hΓ hΓΔ hx hy hxy) _ h1
    _ ⟨ho, hoΓ⟩

omit [Field k] in
theorem card_ne_three [Field k] [Finite k] [CharP k 2] : Nat.card k ≠ 3 := by
  intro h
  have : Fintype k := Fintype.ofFinite k
  have h0 := FiniteField.cast_card_eq_zero k
  rw [Fintype.card_eq_nat_card, h] at h0
  have := (CharP.cast_eq_zero_iff k 2 3).mp h0
  omega

theorem ncard_secant_diff [Finite k] [CharP k 2] [Finite V] [FiniteDimensional k V]
    (hn : 3 ≤ finrank k V) {Δ : Set (ℙ k V)} (hΔ : Δ ∈ C.P) {x y : ℙ k V} (hx : x ∈ Δ)
    (hy : y ∈ Δ) (hxy : x ≠ y) : (pointsIn (line x y) \ Δ).ncard = 1 := by
  set O := pointsIn (line x y) \ Δ with hO
  have hsum : C.l + O.ncard = Nat.card k + 1 := by
    rw [← C.ncard_secant hΔ hx hy hxy, ← ncard_pointsIn_line hxy]
    exact Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _
  have hO1 : 1 ≤ O.ncard := by
    obtain ⟨o, ho, hoΔ⟩ := C.exists_notMem_secant hΔ hx hy hxy
    exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨o, ho, hoΔ⟩
  by_contra hne
  obtain ⟨o₁, o₂, ho₁, ho₂, ho12⟩ := (Set.one_lt_ncard_iff (Set.toFinite O)).mp (by omega)
  have hfix : ∀ {h : V ≃ₗ[k] V}, h ∈ C.K → line (h • x) (h • y) = line x y →
      ∀ o ∈ O, h • o = o :=
    fun hK hL o ho => C.smul_eq_self_of_notMem hn hΔ hx hy hxy hK hL ho.1 ho.2
  have hlx : line o₁ o₂ = line x y := line_eq_line_of_mem hxy ho12 ho₁.1 ho₂.1
  have hxo : ∀ o ∈ O, o ≠ x := fun o ho e => ho.2 (e ▸ hx)
  by_cases h3 : 3 ≤ O.ncard
  · obtain ⟨a₁, a₂, a₃, ha₁, ha₂, ha₃, h12, h13, h23⟩ :=
      (Set.two_lt_ncard_iff (Set.toFinite O)).mp h3
    obtain ⟨h, hK, hhx, hhy⟩ := C.twoTransitive Δ hΔ x hx y hy y hy x hx hxy hxy.symm
    have hL : line (h • x) (h • y) = line x y := by rw [hhx, hhy, line_comm]
    have hl' : line a₁ a₂ = line x y := line_eq_line_of_mem hxy h12 ha₁.1 ha₂.1
    have hfx := smul_eq_self_of_three_fixed h12 h13 h23 (hl' ▸ ha₃.1) (hfix hK hL _ ha₁)
      (hfix hK hL _ ha₂) (hfix hK hL _ ha₃) (hl' ▸ left_mem_pointsIn_line x y)
    exact hxy (hfx.symm.trans hhx)
  · have hO2 : O.ncard = 2 := by omega
    have hb := card_ne_three (k := k)
    have hl2 : 1 < C.l := by
      rw [← C.ncard_secant hΔ hx hy hxy]
      exact (Set.one_lt_ncard_iff (Set.toFinite _)).mpr
        ⟨x, y, ⟨left_mem_pointsIn_line x y, hx⟩, ⟨right_mem_pointsIn_line x y, hy⟩, hxy⟩
    have hl3 : ({x, y} : Set (ℙ k V)).ncard < (pointsIn (line x y) ∩ Δ).ncard := by
      rw [Set.ncard_pair hxy, C.ncard_secant hΔ hx hy hxy]
      omega
    obtain ⟨z, hz, hzxy⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hl3
    have hzx : z ≠ x := fun e => hzxy (e ▸ Set.mem_insert x {y})
    have hzy : z ≠ y := fun e => hzxy (e ▸ Set.mem_insert_of_mem x rfl)
    obtain ⟨h, hK, hhx, hhy⟩ := C.twoTransitive Δ hΔ x hx y hy x hx z hz.2 hxy hzx.symm
    have hL : line (h • x) (h • y) = line x y := by
      rw [hhx, hhy]
      exact line_eq_of_mem hxy hz.1 hzx
    have hfy := smul_eq_self_of_three_fixed ho12 (hxo o₁ ho₁) (hxo o₂ ho₂)
      (hlx ▸ left_mem_pointsIn_line x y) (hfix hK hL _ ho₁) (hfix hK hL _ ho₂) hhx
      (hlx ▸ right_mem_pointsIn_line x y)
    exact hzy (hhy.symm.trans hfy)

theorem l_eq [Finite k] [CharP k 2] [Finite V] [FiniteDimensional k V]
    (hn : 3 ≤ finrank k V) : C.l = Nat.card k := by
  obtain ⟨Δ, hΔ⟩ := C.exists_block
  obtain ⟨x, hx, y, hy, hxy⟩ := C.exists_pair hΔ
  have h := Set.ncard_inter_add_ncard_sdiff_eq_ncard (pointsIn (line x y)) Δ
  rw [C.ncard_secant hΔ hx hy hxy, C.ncard_secant_diff hn hΔ hx hy hxy,
    ncard_pointsIn_line hxy] at h
  omega

theorem exists_partner [Finite k] [CharP k 2] [Finite V] [FiniteDimensional k V]
    (hn : 3 ≤ finrank k V) {Δ : Set (ℙ k V)} (hΔ : Δ ∈ C.P) :
    ∃ Γ ∈ C.P, Γ ≠ Δ ∧ ∀ x ∈ Δ, ∀ y ∈ Δ, x ≠ y → ∀ o ∈ pointsIn (line x y), o ∉ Δ → o ∈ Γ := by
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy₀⟩ := C.exists_pair hΔ
  obtain ⟨o₀, ho₀, ho₀Δ⟩ := C.exists_notMem_secant hΔ hx₀ hy₀ hxy₀
  obtain ⟨Γ, ⟨hΓ, ho₀Γ⟩, -⟩ := C.existsUnique o₀
  refine ⟨Γ, hΓ, fun e => ho₀Δ (e ▸ ho₀Γ), fun x hx y hy hxy o ho hoΔ => ?_⟩
  obtain ⟨h, hK, hhx, hhy⟩ := C.twoTransitive Δ hΔ x₀ hx₀ y₀ hy₀ x hx y hy hxy₀ hxy
  have h1 : h • o₀ ∈ pointsIn (line x y) \ Δ := by
    refine ⟨?_, fun e => ho₀Δ ((C.smul_mem_iff hK hΔ).mp e)⟩
    rw [← hhx, ← hhy]
    exact smul_mem_pointsIn_line_iff.mpr ho₀
  have h2 : h • o₀ = o := (Set.ncard_le_one (Set.toFinite _)).mp
    (C.ncard_secant_diff hn hΔ hx hy hxy).le _ h1 _ ⟨ho, hoΔ⟩
  rw [← h2]
  exact (C.smul_mem_iff hK hΓ).mpr ho₀Γ

end BlockConfig

end CFSG.ShultStronglyClosedTI.Singer
