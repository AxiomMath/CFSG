module

public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGPGLTorality
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBReduce
public import CFSG.LocalAnalysis.StandardType.GGTableBBstar
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace TypeA

variable {d p : ℕ} {K : Type} [Field K]

theorem card_le_of_subset_conjAut_gen [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1) (hd : 0 < d) {X : Subgroup (MulAut (projectiveSL d K))}
    (hX : IsElemAbelian p X)
    (hXI : (X : Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K)) :
    Nat.card X ≤ p ^ (d - 1) := by
  have h1 := PGLTor.card_le_of_isProjElem hp hp2 hpK (isProjElem_comap hd hX)
  rw [card_comap_eq hd hXI, Fintype.card_fin] at h1
  have hK1 : 0 < Nat.card K - 1 := by
    have := Finite.one_lt_card (α := K)
    omega
  have h2 : p * Nat.card X ≤ p ^ d := by
    refine Nat.le_of_mul_le_mul_right ?_ hK1
    calc p * Nat.card X * (Nat.card K - 1) = p * (Nat.card X * (Nat.card K - 1)) := by ring
      _ ≤ p ^ d * (Nat.card K - 1) := h1
  have hd1 : p ^ d = p * p ^ (d - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hd1] at h2
  exact Nat.le_of_mul_le_mul_left h2 hp.pos

end TypeA

theorem ggHasLabel_typeA {X : Type} [Group X] {n f : ℕ}
    (h : StatedClassicalModel X .PSL (n + 1) 2 f) : GGHasLabel ⟨.A, n, f⟩ X := by
  obtain ⟨-, K, hF, hfin, hK, ⟨e⟩⟩ := h
  refine ⟨K, hF, hfin, hK, ⟨?_⟩⟩
  exact ((e.trans (LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj (n + 1) K).symm).trans
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL (n + 1) K)).trans
    (TypeA.recipeEquiv (n + 1) K).symm

theorem largeEvenInLambda2_typeA {X : Type} [Group X] {n f : ℕ}
    (h : StatedClassicalModel X .PSL (n + 1) 2 f) : LargeEvenInLambda2 ⟨.A, n, f⟩ := by
  have hf : 1 ≤ f := h.1.2.1
  have hn : 1 ≤ n := by
    have h2 := h.1.2.2.1
    omega
  have hne : (n + 1, 2 ^ f) ≠ (2, 2) := h.1.2.2.2.1
  refine ⟨hf, hn, ?_⟩
  change n = 1 → 2 ≤ f
  intro h1
  by_contra hf2
  have hf1 : f = 1 := by omega
  exact hne (by simp [h1, hf1])

theorem recipeLinear_rank_le {d N p : ℕ} (hp : p.Prime) (hpN : p ∣ N - 1)
    (hN : ∃ m, N = 2 ^ m) (hd : 1 ≤ d) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeLinear d N Q) :
    LargeEvenRecipeLinear d N fun R _ I F => Q R I F ∧
      ∀ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X →
        Nat.card X ≤ p ^ (d - 1) := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  obtain ⟨m, rfl⟩ := hN
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, pow_zero] at hK
      omega
    · exact h0
  have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpN
  have hp2 : p ≠ 2 := TypeA.prime_ne_two_of_dvd_two_pow_sub_one hm (hK ▸ hpK)
  have hI : ∀ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ,
      MulAut.congr (TypeA.recipeEquiv d K) φ ∈ Set.range (conjAut d K) := fun _ hφ =>
    TypeA.congr_recipeEquiv_mem hφ
  intro X hXI hX
  have hc : Nat.card (X.map (MulAut.congr (TypeA.recipeEquiv d K)).toMonoidHom) =
      Nat.card X := Subgroup.card_map_of_injective (MulAut.congr (TypeA.recipeEquiv d K)).injective
  rw [← hc]
  exact TypeA.card_le_of_subset_conjAut_gen hp hp2 hpK (by omega) (TableB.isElemAbelian_map hX _)
    (by rintro _ ⟨φ, hφ, rfl⟩; exact hI φ (hXI hφ))

theorem largeEvenLabelAll_rank_typeA {p n f : ℕ} (hp : p.Prime) (hpf : p ∣ 2 ^ f - 1) :
    LargeEvenLabelAll ⟨.A, n, f⟩ fun R _ I _ =>
      ∀ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X →
        Nat.card X ≤ p ^ n := by
  intro Q hQ
  have h := recipeLinear_rank_le (d := n + 1) (N := 2 ^ f) hp (by simpa using hpf) ⟨f, rfl⟩
    (by omega) hQ
  exact h

theorem ggInnerDiagOn_split_of_typeA (hRig : GGLabelRigidInput) {G : Type} [Group G]
    {p n f : ℕ} (hp : p.Prime) {Bs K : Subgroup G} (h : GGInnerDiagOn Bs K)
    (hmod : StatedClassicalModel (↥K ⧸ Subgroup.center ↥K) .PSL (n + 1) 2 f)
    (hpf : p ∣ 2 ^ f - 1) : LargeEvenMarking ↥K fun lab _ _ _ _ _ => GGNbrSplitLabel p lab := by
  have hf : 1 ≤ f := hmod.1.2.1
  have hf2 : 2 ≤ f := by
    by_contra hf2
    have hf1 : f = 1 := by omega
    rw [hf1] at hpf
    exact hp.one_lt.ne' (Nat.dvd_one.mp (by simpa using hpf))
  have hmark := ggInnerDiagOn_relabel hRig h (largeEvenInLambda2_typeA hmod)
    (ggHasLabel_typeA hmod)
  refine largeEvenMarking_mono (fun lab' R _ I F θ hP => ?_) hmark
  rw [hP.1]
  exact ⟨trivial, hf2, hpf⟩

section Config

variable {G : Type} [Group G] [Finite G]

theorem GGConfig.card_bstar_le_of_typeA_marking {p n f : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, n, f⟩) p Bs L)
    (hpf : p ∣ 2 ^ f - 1) : Nat.card Bs ≤ p ^ (n + 1) := by
  obtain ⟨hp, -, -, -, -⟩ := hcfg.tableB_facts
  have hmark' := largeEvenMarking_and_labelAll (S := fun lab' => lab' = ⟨.A, n, f⟩)
    (P' := fun R _ I _ => ∀ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I →
      IsElemAbelian p X → Nat.card X ≤ p ^ n)
    (fun lab' _ h' => by rw [h']; exact largeEvenLabelAll_rank_typeA hp hpf)
    (fun lab' R _ I F θ hPmark => hPmark.1) hmark
  obtain ⟨hL, lab', hlab', hraw'⟩ := hmark'
  obtain ⟨R, _, I, F, -, -, θ, hPθ⟩ := largeEvenRawDatum_exists hraw'
  obtain ⟨⟨-, hN, hind⟩, hrank⟩ := hPθ
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hBsG : GGBstar p B Bs := hcfg.2.1
  have hcard := card_range_ggBeta_mul_of hp hBsG.2.1 (hBsG.1 hS.2.1) hS.2.2.1 hS.2.2.2.1.1
    hS.2.2.2.2 hL θ hN
  have hXI : (((ggBeta L θ hN).range : Subgroup (MulAut R)) : Set (MulAut R)) ⊆ I := by
    rintro _ ⟨b, rfl⟩
    exact ggBeta_mem L θ hN hind b
  have hle := hrank _ hXI (isElemAbelian_range_ggBeta θ hBsG.2.1 hN)
  calc Nat.card Bs = Nat.card (ggBeta L θ hN).range * p := hcard.symm
    _ ≤ p ^ n * p := Nat.mul_le_mul_right p hle
    _ = p ^ (n + 1) := (pow_succ p n).symm

theorem GGConfig.card_bstar_le_of_typeA (hRig : GGLabelRigidInput) {p n f : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hInn : GGInnerDiagOn Bs L)
    (hmod : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL (n + 1) 2 f)
    (hpf : p ∣ 2 ^ f - 1) : Nat.card Bs ≤ p ^ (n + 1) :=
  hcfg.card_bstar_le_of_typeA_marking
    (ggInnerDiagOn_relabel hRig hInn (largeEvenInLambda2_typeA hmod)
      (ggHasLabel_typeA hmod)) hpf

theorem GGConfig.three_le_rank_of_typeA_marking {p n f : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, n, f⟩) p Bs L)
    (hpf : p ∣ 2 ^ f - 1) : 3 ≤ n := by
  obtain ⟨hp, -, -, -, h4⟩ := hcfg.tableB_facts
  have hle : p ^ 4 ≤ p ^ (n + 1) := h4.trans
    (hcfg.card_bstar_le_of_typeA_marking hmark hpf)
  have : 4 ≤ n + 1 := (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
  omega

end Config

end CFSG.StandardType

end
