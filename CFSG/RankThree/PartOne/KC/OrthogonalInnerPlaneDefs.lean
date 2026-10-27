module

public import CFSG.RankThree.PartOne.KC.OrthogonalFixedCoverage
public import CFSG.RankThree.PartOne.KC.OrthogonalBinaryDickson

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module CFSG CFSG.RankThree.LocalRank CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.Classical2

section Defs

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def FixedLayerListed (Q : QuadraticForm K V) (x : V ≃ₗ[K] V) : Prop :=
  3 ≤ finrank K (fixedSpace x) ∧ ¬ SmallFixedException (Q.comp (fixedSpace x).subtype)

open scoped _root_.Classical in
@[expose] noncomputable def fixedLayerImage (Q : QuadraticForm K V) (x : V ≃ₗ[K] V) :
    Subgroup (ProjOrthDerived Q) :=
  if FixedLayerListed Q x then fixedComponentImage Q x else ⊥

end Defs

section Helpers

theorem normal_subgroupOf_iSup {G : Type*} [Group G] {N : Subgroup G} {ι : Sort*}
    (J : ι → Subgroup G) (hJ : ∀ i, J i ≤ N) (hn : ∀ i, ((J i).subgroupOf N).Normal) :
    ((⨆ i, J i).subgroupOf N).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (iSup_le hJ)]
  intro h k hh hk
  have hle : (⨆ i, J i).map (MulAut.conj k).toMonoidHom ≤ ⨆ i, J i := by
    rw [Subgroup.map_iSup]
    refine iSup_mono fun i => ?_
    rintro _ ⟨j, hj, rfl⟩
    exact (Subgroup.normal_subgroupOf_iff (hJ i)).mp (hn i) j k hj hk
  have := hle ⟨h, hh, rfl⟩
  simpa using this

theorem ne_bot_of_isQuasisimple {G : Type*} [Group G] {J : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥J) : J ≠ ⊥ := by
  rintro rfl
  obtain ⟨a, b, hab⟩ := hq.2.2
  have : Subsingleton ↥(⊥ : Subgroup G) := inferInstance
  have : Subsingleton (↥(⊥ : Subgroup G) ⧸ Subgroup.center ↥(⊥ : Subgroup G)) :=
    inferInstance
  exact hab (Subsingleton.elim _ _)

end Helpers

section Layer

variable {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

omit [Finite K] in
theorem OddOrderIsometry.eq_one_of_restrictFixed_eq_one (hx : OddOrderIsometry Q p x)
    {w₀ : V ≃ₗ[K] V} (hw : w₀ ∈ supportedBlock Q x (X - 1))
    (h : restrictFixed Q x ⟨w₀, hw⟩ = 1) : w₀ = 1 := by
  have := restrictFixed_injective hx (a₁ := ⟨w₀, hw⟩) (a₂ := 1) (by rw [h, map_one])
  exact congrArg Subtype.val this

theorem OddOrderIsometry.fixedLayer_data (hx : OddOrderIsometry Q p x)
    (hlist : FixedLayerListed Q x) :
    ∃ (n : ℕ) (C : Fin n → Subgroup (ProjOrthDerived Q)), 1 ≤ n ∧ n ≤ 2 ∧
      (⨆ i, C i) = fixedComponentImage Q x ∧
      (∀ i, CFSG.IsQuasisimple ↥(C i) ∧ C i ≤ centralizerImage Q x ∧
        ((C i).subgroupOf (centralizerImage Q x)).IsSubnormal) ∧
      (∀ i j, i ≠ j → ∀ u ∈ C i, ∀ v ∈ C j, u * v = v * u) ∧
      ∀ g ∈ supportedBlock Q x (X - 1), ∀ q : ℕ, q.Prime → 3 < q → g ^ q = 1 →
        g ∈ supportedFixedDerived Q x := by
  have hQW := hx.polarBilin_fixed_nondegenerate
  by_cases hT : ∃ U : Submodule K (fixedSpace x), finrank K U = 3 ∧
      ∀ u ∈ U, (Q.comp (fixedSpace x).subtype) u = 0
  · refine ⟨1, fun _ => fixedComponentImage Q x, le_rfl, by norm_num, iSup_const,
      fun _ => ⟨hx.isQuasisimple_fixedComponentImage hT, fixedComponentImage_le_centralizerImage,
        ?_⟩, fun i j hij => absurd (Subsingleton.elim i j) hij, ?_⟩
    · exact hx.normal_fixedComponentImage.isSubnormal
    · intro g hg q hq hq3 hgq
      exact hx.mem_supportedFixedDerived_of_odd_pow hT hg (hq.odd_of_ne_two (by omega)) hgq
  · obtain ⟨-, h2⟩ := orthogonal_regular_space_coverage (Q.comp (fixedSpace x).subtype) hQW
      hlist.1
    exact hx.exists_fixedLayer_components (h2 hlist.2)

theorem OddOrderIsometry.residue_cases (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp3 : 3 < p)
    {w₀ : V ≃ₗ[K] V} (hw : w₀ ∈ supportedBlock Q x (X - 1)) (hwp : w₀ ^ p = 1) :
    w₀ = 1 ∨ finrank K (fixedSpace x) = 2 ∨
      (FixedLayerListed Q x ∧ w₀ ∈ supportedFixedDerived Q x) := by
  have hQW := hx.polarBilin_fixed_nondegenerate
  have hp2 : Odd p := hp.odd_of_ne_two (by omega)
  set g : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) :=
    ⟨restrictFixed Q x ⟨w₀, hw⟩, restrictFixed_mem_orthogonalGroup _⟩ with hg
  have hgp : g ^ p = 1 := Subtype.ext (by
    show (restrictFixed Q x ⟨w₀, hw⟩) ^ p = 1
    rw [← map_pow]
    have : (⟨w₀, hw⟩ : ↥(supportedBlock Q x (X - 1))) ^ p = 1 := Subtype.ext hwp
    rw [this, map_one])
  by_cases h1 : finrank K (fixedSpace x) ≤ 1
  · left
    exact hx.eq_one_of_restrictFixed_eq_one hw (eq_one_of_finrank_le_one hQW h1 hp2 hgp)
  by_cases h2 : finrank K (fixedSpace x) = 2
  · exact Or.inr (Or.inl h2)
  have h3 : 3 ≤ finrank K (fixedSpace x) := by omega
  by_cases hlist : FixedLayerListed Q x
  · obtain ⟨n, C, -, -, -, -, -, hmem⟩ := hx.fixedLayer_data hlist
    exact Or.inr (Or.inr ⟨hlist, hmem w₀ hw p hp hp3 hwp⟩)
  · left
    have hexc : SmallFixedException (Q.comp (fixedSpace x).subtype) := by
      by_contra hne
      exact hlist ⟨h3, hne⟩
    obtain ⟨h4, -⟩ := orthogonal_regular_space_coverage (Q.comp (fixedSpace x).subtype) hQW h3
    have h5 := h4 hexc g p hp hp3
    have h6 : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgp
    rcases (Nat.dvd_prime hp).mp h6 with h7 | h7
    · have hg1 : g = 1 := orderOf_eq_one_iff.mp h7
      exact hx.eq_one_of_restrictFixed_eq_one hw (congrArg Subtype.val hg1)
    · exact absurd h7 h5

end Layer

section LayerImage

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

omit [FiniteDimensional K V] in
theorem fixedLayerImage_of_listed (h : FixedLayerListed Q x) :
    fixedLayerImage Q x = fixedComponentImage Q x := by
  simp [fixedLayerImage, h]

omit [FiniteDimensional K V] in
theorem fixedLayerImage_le_centralizerImage : fixedLayerImage Q x ≤ centralizerImage Q x := by
  unfold fixedLayerImage
  split_ifs
  · exact fixedComponentImage_le_centralizerImage
  · exact bot_le

theorem OddOrderIsometry.normal_fixedLayerImage (hx : OddOrderIsometry Q p x) :
    ((fixedLayerImage Q x).subgroupOf (centralizerImage Q x)).Normal := by
  unfold fixedLayerImage
  split_ifs
  · exact hx.normal_fixedComponentImage
  · rw [Subgroup.bot_subgroupOf]
    exact Subgroup.normal_bot

theorem normal_subgroupOf_sup {G : Type*} [Group G] {N J₁ J₂ : Subgroup G} (h₁ : J₁ ≤ N)
    (h₂ : J₂ ≤ N) (n₁ : (J₁.subgroupOf N).Normal) (n₂ : (J₂.subgroupOf N).Normal) :
    ((J₁ ⊔ J₂).subgroupOf N).Normal := by
  have := normal_subgroupOf_iSup (N := N) (fun b : Bool => if b then J₁ else J₂)
    (fun b => by cases b <;> simp [h₁, h₂]) (fun b => by cases b <;> simp [n₁, n₂])
  rwa [iSup_bool_eq] at this

end LayerImage

section Product

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem componentProduct_le_centralizerImage {x : V ≃ₗ[K] V} (Rep : Finset K[X]) :
    componentProduct Q x Rep ≤ centralizerImage Q x :=
  iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => componentImage_le_centralizerImage

theorem normal_componentProduct {x : V ≃ₗ[K] V} (Rep : Finset K[X]) :
    ((componentProduct Q x Rep).subgroupOf (centralizerImage Q x)).Normal := by
  unfold componentProduct
  refine normal_subgroupOf_iSup _ (fun h => iSup_le fun _ => iSup_le fun _ =>
    componentImage_le_centralizerImage) (fun h => ?_)
  refine normal_subgroupOf_iSup _ (fun _ => iSup_le fun _ => componentImage_le_centralizerImage)
    (fun _ => ?_)
  exact normal_subgroupOf_iSup _ (fun _ => componentImage_le_centralizerImage)
    (fun _ => normal_componentImage)

end Product

end CFSG.RankThree.PartOne.KCOrthogonal
