module

public import CFSG.RankThree.PartOne.SLB4B.RankFourSp
public import CFSG.RankThree.PartOne.SLB4B.CoverKer

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.SLB4B

open Matrix Subgroup CFSG CFSG.RankThree.PartOne.SRC CFSG.RankThree.PartTwo.Census
  CFSG.RankThree.Classical CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open CFSG.LieType.Steinberg.Sp (blockMat)
open scoped MatrixGroups

section Prod

variable {K : Type} [Field K]

theorem commute_planeInvolution {x : StatedSp 3 K} (hx : x ∈ suppGroup (coords (0 : Fin 3))) :
    Commute (planeInvolution 3 K) x := by
  have hx' : IsSupp (coords (0 : Fin 3)) (mat 3 K x) := hx
  apply Subtype.ext
  apply Units.ext
  change ((planeInvolution 3 K : StatedSp 3 K) : GL (Fin 3 ⊕ Fin 3) K).val *
    ((x : StatedSp 3 K) : GL (Fin 3 ⊕ Fin 3) K).val =
    ((x : StatedSp 3 K) : GL (Fin 3 ⊕ Fin 3) K).val *
      ((planeInvolution 3 K : StatedSp 3 K) : GL (Fin 3 ⊕ Fin 3) K).val
  rw [coe_planeInvolution, Matrix.fromBlocks_diagonal]
  ext r s
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hrs : r = s
  · subst hrs
    exact mul_comm _ _
  by_cases hM : ((x : StatedSp 3 K) : GL (Fin 3 ⊕ Fin 3) K).val r s = 0
  · simp [hM]
  · have hmem : r ∈ coords (0 : Fin 3) ∧ s ∈ coords (0 : Fin 3) := by
      by_contra hno
      apply hM
      rw [show ((x : StatedSp 3 K) : GL (Fin 3 ⊕ Fin 3) K).val r s =
        (1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) r s from hx' r s hno,
        Matrix.one_apply_ne hrs]
    obtain ⟨hr, hs⟩ := hmem
    rcases mem_coords.mp hr with rfl | rfl <;> rcases mem_coords.mp hs with rfl | rfl <;>
      simp [planeSign]

@[expose] noncomputable def rootPlane0 : Multiplicative K →* StatedSp 3 K :=
  (longBlock K 3 0).comp CFSG.SL2MinimalFaithful.unipotentHom

theorem rootPlane0_mem (v : Multiplicative K) :
    rootPlane0 v ∈ suppGroup (coords (0 : Fin 3)) := by
  rw [← range_longBlock]
  exact ⟨CFSG.SL2MinimalFaithful.unipotentHom v, rfl⟩

theorem rootPlane0_injective : Function.Injective (rootPlane0 (K := K)) :=
  (longBlock_injective 0).comp CFSG.SL2MinimalFaithful.unipotentHom_injective

theorem rootPlane0_entry (v : Multiplicative K) :
    mat 3 K (rootPlane0 v) (Sum.inl 0) (Sum.inl 0) = 1 := by
  change blockMat (Sum.inl (0 : Fin 3)) (Sum.inr 0)
    ((CFSG.SL2MinimalFaithful.unipotentHom v : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) (Sum.inl 0) (Sum.inl 0) = 1
  simp [blockMat, CFSG.SL2MinimalFaithful.unipotentHom, CFSG.SL2MinimalFaithful.coe_unipotent]

theorem spEmbed_mem_suppGroup_compl (g : StatedSp 2 K) :
    spEmbed planes12 planes12_injective g ∈ suppGroup (coords (0 : Fin 3))ᶜ := by
  refine suppGroup_mono ?_ (isSupp_spEmbed planes12_injective g)
  rintro _ ⟨a, rfl⟩ hmem
  exact map_planes12_ne_inl_zero a hmem

theorem spEmbed_comm_rootPlane0 (g : StatedSp 2 K) (v : Multiplicative K) :
    Commute (spEmbed planes12 planes12_injective g) (rootPlane0 v) :=
  (commute_suppGroup_compl (rootPlane0_mem v) (spEmbed_mem_suppGroup_compl g)).symm

@[expose] noncomputable def sp6Prod : StatedSp 2 K × Multiplicative K →* StatedSp 3 K :=
  MonoidHom.noncommCoprod (spEmbed planes12 planes12_injective) rootPlane0
    spEmbed_comm_rootPlane0

theorem sp6Prod_apply (g : StatedSp 2 K) (v : Multiplicative K) :
    sp6Prod (g, v) = spEmbed planes12 planes12_injective g * rootPlane0 v := rfl

@[expose] noncomputable def sp6ProdProj : StatedSp 2 K × Multiplicative K →*
    StatedProj (StatedSp 3 K) :=
  (QuotientGroup.mk' ((StatedScalars (Fin 3 ⊕ Fin 3) K).subgroupOf (StatedSp 3 K))).comp sp6Prod

theorem inl_zero_not_mem_range :
    (Sum.inl (0 : Fin 3) : Fin 3 ⊕ Fin 3) ∉ Set.range (Sum.map planes12 planes12) := by
  rintro ⟨a, ha⟩
  exact map_planes12_ne_inl_zero a (by rw [ha]; exact mem_coords.mpr (Or.inl rfl))

theorem sp6ProdProj_injective : Function.Injective (sp6ProdProj (K := K)) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨g, v⟩ hg
  rw [sp6ProdProj, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf, sp6Prod_apply] at hg
  obtain ⟨u, hu⟩ := hg
  have h := congrArg (fun x : GL (Fin 3 ⊕ Fin 3) K => (x : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K))
    hu
  have e := congrFun (congrFun h (Sum.inl 0)) (Sum.inl 0)
  have hrow : ∀ s, mat 3 K (spEmbed planes12 planes12_injective g) (Sum.inl 0) s =
      (1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) (Sum.inl 0) s := fun s =>
    isSupp_spEmbed planes12_injective g (Sum.inl 0) s (fun h' => inl_zero_not_mem_range h'.1)
  have e1 : mat 3 K (spEmbed planes12 planes12_injective g * rootPlane0 v) (Sum.inl 0)
      (Sum.inl 0) = 1 := by
    rw [map_mul, Matrix.mul_apply, Finset.sum_congr rfl (fun s _ => by rw [hrow s]),
      ← Matrix.mul_apply, Matrix.one_mul]
    exact rootPlane0_entry v
  have hu0 : (u : K) = 1 := by
    have e2 : (((spEmbed planes12 planes12_injective g * rootPlane0 v : StatedSp 3 K) :
        GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) (Sum.inl 0) (Sum.inl 0) =
        1 := e1
    rw [e2] at e
    simpa [Matrix.GeneralLinearGroup.coe_scalar] using e
  have hu1 : u = 1 := Units.ext hu0
  subst hu1
  have hprod : spEmbed planes12 planes12_injective g * rootPlane0 v = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [← hu]
    simp
  have hdis := disjoint_suppGroup_compl (K := K) (n := 3) (coords (0 : Fin 3))
  rw [Subgroup.disjoint_def] at hdis
  have heq : spEmbed planes12 planes12_injective g = (rootPlane0 v)⁻¹ :=
    eq_inv_of_mul_eq_one_left hprod
  have hv1 : (rootPlane0 v)⁻¹ = 1 :=
    hdis (Subgroup.inv_mem _ (rootPlane0_mem v)) (heq ▸ spEmbed_mem_suppGroup_compl g)
  have hv : v = 1 := rootPlane0_injective (by
    have := inv_eq_one.mp hv1
    rw [this, map_one])
  have hg1 : g = 1 := spEmbed_injective planes12_injective (by
    rw [heq, hv1, map_one])
  rw [hg1, hv]
  rfl

theorem sp6ProdProj_comm (g : StatedSp 2 K × Multiplicative K) :
    sp6ProdProj g * sp6Invol = sp6Invol * sp6ProdProj g := by
  obtain ⟨a, v⟩ := g
  have h1 : Commute (planeInvolution 3 K) (rootPlane0 v) :=
    commute_planeInvolution (rootPlane0_mem v)
  have h2 : Commute (planeInvolution 3 K) (spEmbed planes12 planes12_injective a) :=
    commute_suppGroup_compl planeInvolution_mem_suppGroup_zero (spEmbed_mem_suppGroup_compl a)
  have h3 := h2.mul_right h1
  rw [sp6ProdProj, sp6Invol, MonoidHom.comp_apply, sp6Prod_apply, ← map_mul, ← map_mul, ← h3.eq]

variable [Finite K]

theorem fst_cover_data {p : ℕ} [Fact p.Prime] (hK : Nat.card K = p) (W : Type) [Group W]
    (ρ : W →* StatedSp 2 K × Multiplicative K) (hρ : Function.Surjective ρ)
    (hker : IsPGroup p ρ.ker) :
    Function.Surjective ((MonoidHom.fst _ _).comp ρ) ∧
      IsPGroup p ((MonoidHom.fst _ _).comp ρ).ker ∧ ((MonoidHom.fst _ _).comp ρ).ker ≠ ⊥ := by
  have hp : p.Prime := Fact.out
  set π : W →* StatedSp 2 K := (MonoidHom.fst _ _).comp ρ with hπdef
  have hπ : Function.Surjective π := fun a => by
    obtain ⟨w, hw⟩ := hρ (a, 1)
    exact ⟨w, by simp [π, hw]⟩
  have hUp : ∀ u : Multiplicative K, u ^ p = 1 := fun u => by
    rw [← hK]
    exact pow_card_eq_one'
  have hπker : IsPGroup p π.ker := by
    intro g
    have hg : (ρ (g : W)).1 = 1 := g.2
    have hρg : ρ (g : W) ^ p = 1 := Prod.ext (by simp [hg]) (hUp (ρ (g : W)).2)
    have hmem : (g : W) ^ p ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact hρg
    obtain ⟨n, hn⟩ := hker ⟨(g : W) ^ p, hmem⟩
    refine ⟨n + 1, Subtype.ext ?_⟩
    have h1 : ((g : W) ^ p) ^ (p ^ n) = 1 := by simpa using congrArg Subtype.val hn
    change (g : W) ^ (p ^ (n + 1)) = 1
    rw [pow_succ', pow_mul]
    exact h1
  have hker1 : π.ker ≠ ⊥ := by
    have hu : (Multiplicative.ofAdd (1 : K)) ≠ 1 := by
      intro h
      have : Nontrivial K := Finite.one_lt_card_iff_nontrivial.mp (by rw [hK]; exact hp.one_lt)
      exact one_ne_zero (ofAdd_eq_one.mp h)
    obtain ⟨w, hw⟩ := hρ (1, Multiplicative.ofAdd 1)
    intro hbot
    have hw1 : w ∈ π.ker := congrArg Prod.fst hw
    rw [hbot, Subgroup.mem_bot] at hw1
    rw [hw1, map_one] at hw
    exact hu (congrArg Prod.snd hw).symm
  exact ⟨hπ, hπker, hker1⟩

theorem cover_sp4_prod {p : ℕ} [Fact p.Prime] [CharP K p] (hK : Nat.card K = p) (hp2 : p ≠ 2)
    (h5 : 5 ≤ p) (W : Type) [Group W] [Finite W] (ρ : W →* StatedSp 2 K × Multiplicative K)
    (hρ : Function.Surjective ρ) (hker : IsPGroup p ρ.ker) :
    ∃ (E : Subgroup W) (k : ℕ), 4 ≤ k ∧ IsElementaryAbelian p E ∧ Nat.card E = p ^ k := by
  obtain ⟨hπ, hπker, hker1⟩ := fst_cover_data hK W ρ hρ hker
  have hK1 : Nat.card K = p ^ 1 := by rw [pow_one]; exact hK
  exact rank_four_of_cover_quasisimple_ker hp2 (sp4_quasisimple (by omega)) sp4_coprime_center _
    (planeInvolution_noncentral hp2) (planeInvolution_coprime hp2) (pow_four_dvd_card_sp4 hK1 le_rfl)
    (sp4_closed (by omega)) isElementaryAbelian_siegelSp
    (by rw [card_siegelSp_range hK1, mul_one]) _ hπ hπker hker1

theorem rankFourCover_psp6_of_five_le {p e : ℕ} [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = p ^ e) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ e) :
    RankFourCover p (StatedProj (StatedSp 3 K)) := by
  have hp : p.Prime := Fact.out
  rcases Nat.lt_or_ge e 2 with he | he
  · have he1 : e = 1 := by
      rcases Nat.eq_zero_or_pos e with rfl | h
      · simp at h5
      · omega
    subst he1
    rw [pow_one] at hK h5
    exact rankFourCover_of_cover_ker hp hp2
      (fun W _ _ ρ hρ hker => cover_sp4_prod hK hp2 h5 W ρ hρ hker) (sp6ProdProj (K := K))
      (fun A hA => by rw [sp6ProdProj_injective (hA.trans (map_one _).symm), one_pow])
      (orderOf_sp6Invol (two_ne_zero_of_charP hp2)) sp6ProdProj_comm
  · exact rankFourCover_psp6 hK hp2 he

end Prod

end CFSG.RankThree.PartOne.SLB4B
