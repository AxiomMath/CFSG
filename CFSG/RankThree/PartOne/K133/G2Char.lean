module

public import CFSG.LieType.Chevalley.ParabolicRadicalLevi
public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.LieType.Chevalley.ChevalleySplitBN
public import CFSG.RankThree.PartOne.K133.LeviSimple

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.BorelTits
  CFSG.Assembly.LowTwoRank

set_option linter.unusedSectionVars false

theorem torusElt_neg_one_ne_one_G2 (K : Type) [Field K] (h2 : (2 : K) ≠ 0) (i : Fin Tag.G2.rank) :
    torusElt .G2 K i (-1) ≠ 1 := by
  intro h
  obtain ⟨k, hk⟩ : ∃ k : Fin Tag.G2.rank, Odd (Tag.cartan .G2 i k) := by
    fin_cases i
    · exact ⟨⟨1, by decide⟩, -1, by decide⟩
    · exact ⟨⟨0, by decide⟩, -2, by decide⟩
  have hv := congrArg (fun g : ModGL .G2 K =>
    (g : Module.End K (RootModule .G2 K)) (rootVec .G2 K (Pi.single k 1))) h
  have hs : ∑ j, Tag.cartan .G2 i j * (Pi.single k 1 : Fin Tag.G2.rank → ℤ) j = Tag.cartan .G2 i k := by
    simp [Pi.single_apply]
  simp only [torusElt_rootVec i (-1) (isRoot_single _ k), hs, Units.val_one,
    Module.End.one_apply] at hv
  rw [rootVec_eq_single_of_isRoot (isRoot_single _ k)] at hv
  have hv' := congrArg (fun v : RootModule .G2 K => v (Sum.inr ⟨_, isRoot_single _ k⟩)) hv
  simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at hv'
  rw [Odd.neg_one_zpow hk] at hv'
  apply h2
  simp only [Units.val_neg, Units.val_one] at hv'
  linear_combination -hv'

theorem rankOne_injective_G2 (K : Type) [Field K] (h2 : (2 : K) ≠ 0) (i : Fin Tag.G2.rank) :
    ∃ ρ : SL2 K →* ModGL .G2 K, Function.Injective ρ ∧
      ρ.range = Subgroup.closure (Set.range (xUnit .G2 K i) ∪ Set.range (yUnit .G2 K i)) := by
  obtain ⟨ρ, hu, hv, hH, hW, hrange, hker, -, -⟩ :=
    exceptional_ordinary_rank_one_central_image .G2 K i
  refine ⟨ρ, ?_, hrange⟩
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨l, hl2, hgl⟩ := hker g (MonoidHom.mem_ker.2 hg)
  have hl : (l : K) = 1 ∨ (l : K) = -1 := by
    have : ((l : K) - 1) * ((l : K) + 1) = 0 := by linear_combination hl2
    rcases mul_eq_zero.1 this with h | h
    · left; linear_combination h
    · right; linear_combination h
  rcases hl with hl | hl
  · apply Subtype.ext
    rw [hgl, hl, one_smul]
    rfl
  · exfalso
    have hg' : g = HSL (-1) := by
      apply Subtype.ext
      rw [hgl, hl]
      ext a b
      fin_cases a <;> fin_cases b <;> simp [HSL]
    rw [hg', hH] at hg
    exact torusElt_neg_one_ne_one_G2 K h2 i hg

@[expose] noncomputable def rankOneGroup (K : Type) [Field K] (i : Fin Tag.G2.rank) : Subgroup (ModGL .G2 K) :=
  Subgroup.closure (Set.range (xUnit .G2 K i) ∪ Set.range (yUnit .G2 K i))

theorem rootSubgroup_single_le_rankOne (K : Type) [Field K] (i : Fin Tag.G2.rank) :
    rootSubgroup .G2 K (Pi.single i 1) ≤ rankOneGroup K i := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  rw [pinnedX_single]
  exact Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)

theorem rootSubgroup_neg_single_le_rankOne (K : Type) [Field K] (i : Fin Tag.G2.rank) :
    rootSubgroup .G2 K (-Pi.single i 1) ≤ rankOneGroup K i := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  rw [pinnedX_neg_single]
  exact Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)

theorem conj_torusElt_xUnit_mem (K : Type) [Field K] (i l : Fin Tag.G2.rank) (u : Kˣ) (c : K) :
    torusElt .G2 K l u * xUnit .G2 K i c * (torusElt .G2 K l u)⁻¹ ∈ rankOneGroup K i := by
  have hmem : (MulAut.conj (torusElt .G2 K l u)).toMonoidHom (xUnit .G2 K i c) ∈
      rootSubgroup .G2 K (Pi.single i 1) := by
    rw [← map_conj_torusElt_rootSubgroup (R := K) l u (isRoot_single .G2 i)]
    exact Subgroup.mem_map_of_mem _ (xUnit_mem_rootSubgroup i c)
  exact rootSubgroup_single_le_rankOne K i hmem

theorem conj_torusElt_yUnit_mem (K : Type) [Field K] (i l : Fin Tag.G2.rank) (u : Kˣ) (c : K) :
    torusElt .G2 K l u * yUnit .G2 K i c * (torusElt .G2 K l u)⁻¹ ∈ rankOneGroup K i := by
  have hmem : (MulAut.conj (torusElt .G2 K l u)).toMonoidHom (yUnit .G2 K i c) ∈
      rootSubgroup .G2 K (-Pi.single i 1) := by
    rw [← map_conj_torusElt_rootSubgroup (R := K) l u (isRoot_neg_single .G2 i)]
    exact Subgroup.mem_map_of_mem _ (yUnit_mem_rootSubgroup i c)
  exact rootSubgroup_neg_single_le_rankOne K i hmem

theorem conj_torusElt_mem_rankOne (K : Type) [Field K] (i l : Fin Tag.G2.rank) (u : Kˣ)
    {d : ModGL .G2 K} (hd : d ∈ rankOneGroup K i) :
    torusElt .G2 K l u * d * (torusElt .G2 K l u)⁻¹ ∈ rankOneGroup K i := by
  unfold rankOneGroup at hd ⊢
  induction hd using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact conj_torusElt_xUnit_mem K i l u c
    · exact conj_torusElt_yUnit_mem K i l u c
  | one => simp
  | mul x y _ _ hx hy =>
    have : torusElt .G2 K l u * (x * y) * (torusElt .G2 K l u)⁻¹ =
        (torusElt .G2 K l u * x * (torusElt .G2 K l u)⁻¹) *
          (torusElt .G2 K l u * y * (torusElt .G2 K l u)⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have : torusElt .G2 K l u * x⁻¹ * (torusElt .G2 K l u)⁻¹ =
        (torusElt .G2 K l u * x * (torusElt .G2 K l u)⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hx

theorem torusGroup_le_normalizer_rankOne (K : Type) [Field K] (i : Fin Tag.G2.rank) :
    torusGroup .G2 K ≤ Subgroup.normalizer (rankOneGroup K i : Set (ModGL .G2 K)) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨⟨l, u⟩, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
  intro d
  have hinv : torusElt .G2 K l u⁻¹ = (torusElt .G2 K l u)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← torusElt_mul, inv_mul_cancel, torusElt_one]
  constructor
  · intro hd
    exact conj_torusElt_mem_rankOne K i l u hd
  · intro hd
    have h := conj_torusElt_mem_rankOne K i l u⁻¹ hd
    rw [hinv] at h
    simpa [mul_assoc] using h

theorem commutator_parabolicLevi_le (K : Type) [Field K] (J : Set (Fin Tag.G2.rank))
    (i : Fin Tag.G2.rank) (hJ : ∀ j ∈ J, j = i) :
    ⁅parabolicLevi .G2 K J, parabolicLevi .G2 K J⁆ ≤ rankOneGroup K i := by
  have hle : parabolicLevi .G2 K J ≤ torusGroup .G2 K ⊔ rankOneGroup K i := by
    refine sup_le_sup_left ((Subgroup.closure_le _).2 ?_) _
    rintro _ ⟨j, hj, c, rfl | rfl⟩
    · rw [hJ j hj]
      exact Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)
    · rw [hJ j hj]
      exact Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)
  refine (Subgroup.commutator_mono hle hle).trans ?_
  refine commutator_sup_le_of_normalizes _ _ (fun a ha b hb => ?_)
    (torusGroup_le_normalizer_rankOne K i)
  exact mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup ha) (torusGroup_le_diagonalGroup hb)

theorem exists_conj_le_parabolic_G2 (K : Type) [Field K] [Finite K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    {U : Subgroup (adjointGroup .G2 K)} (hU : U ≠ ⊥) (hUp : IsPGroup ℓ U) :
    ∃ (g : adjointGroup .G2 K) (J : Set (Fin Tag.G2.rank)), J ≠ Set.univ ∧
      ∀ k ∈ Subgroup.normalizer (U : Set (adjointGroup .G2 K)),
        ((g⁻¹ * k * g : adjointGroup .G2 K) : ModGL .G2 K) ∈ parabolicSubgroup .G2 K J := by
  classical
  have : Finite (ModGL .G2 K) := finite_modGL
  obtain ⟨S, P, hPtop, hNU, -, -, hNS⟩ := holds_adjointGroup_tag .G2 K ℓ U hU hUp
  obtain ⟨hU0p, hU0i⟩ := isPGroup_and_not_dvd_index ℓ
    (posUnipotent_le_adjointGroup (τ := .G2) (K := K)) card_posUnipotent
  let S0 : Sylow ℓ (adjointGroup .G2 K) := hU0p.toSylow hU0i
  have hS0 : (S0 : Subgroup (adjointGroup .G2 K)) = posUnipotentSub .G2 K :=
    IsPGroup.toSylow_coe hU0p hU0i
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (adjointGroup .G2 K) S0 S
  have hSmem : ∀ x : adjointGroup .G2 K,
      x ∈ (S : Subgroup (adjointGroup .G2 K)) ↔ g⁻¹ * x * g ∈ posUnipotentSub .G2 K := by
    intro x
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hS0]
    simp [MulAut.smul_def]
  have hBN : ∀ b ∈ borelGroup .G2 K, b ∈ Subgroup.normalizer (posUnipotent .G2 K : Set (ModGL .G2 K)) := by
    intro b hb
    have hb' : b ∈ adjointGroup .G2 K ⊓ Subgroup.normalizer (posUnipotent .G2 K : Set (ModGL .G2 K)) := by
      rw [(borel_self_normalizers .G2 K).1]
      exact hb
    exact (Subgroup.mem_inf.1 hb').2
  have hB : ∀ b : adjointGroup .G2 K, (b : ModGL .G2 K) ∈ borelGroup .G2 K → g * b * g⁻¹ ∈ P := by
    intro b hb
    apply hNS
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hSmem, hSmem]
    have hbn := Subgroup.mem_normalizer_iff.1 (hBN b hb)
    have e : g⁻¹ * (g * b * g⁻¹ * y * (g * b * g⁻¹)⁻¹) * g = b * (g⁻¹ * y * g) * b⁻¹ := by group
    rw [e]
    have := hbn ((g⁻¹ * y * g : adjointGroup .G2 K) : ModGL .G2 K)
    exact this
  let P' : Subgroup (adjointGroup .G2 K) := P.comap (MulAut.conj g).toMonoidHom
  let P'' : Subgroup (ModGL .G2 K) := P'.map (adjointGroup .G2 K).subtype
  have hP''le : P'' ≤ adjointGroup .G2 K := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hBP'' : borelGroup .G2 K ≤ P'' := by
    intro b hb
    refine ⟨⟨b, borelGroup_le_adjointGroup' hb⟩, ?_, rfl⟩
    show g * (⟨b, borelGroup_le_adjointGroup' hb⟩ : adjointGroup .G2 K) * g⁻¹ ∈ P
    exact hB _ hb
  have hPJ := eq_parabolicSubgroup_of_borelGroup_le hBP'' hP''le
  refine ⟨g, {i | weylElt .G2 K i 1 ∈ P''}, ?_, ?_⟩
  · intro hJ
    have hX := eq_parabolicSubgroup_of_borelGroup_le (A := adjointGroup .G2 K)
      borelGroup_le_adjointGroup' le_rfl
    have hall : {i | weylElt .G2 K i 1 ∈ adjointGroup .G2 K} = Set.univ :=
      Set.eq_univ_of_forall fun i => weylElt_mem_adjointGroup i 1
    rw [hall] at hX
    rw [hJ] at hPJ
    have hP''X : P'' = adjointGroup .G2 K := hPJ.trans hX.symm
    apply hPtop
    rw [eq_top_iff]
    intro z _
    have hz : ((g⁻¹ * z * g : adjointGroup .G2 K) : ModGL .G2 K) ∈ P'' := by
      rw [hP''X]
      exact (g⁻¹ * z * g).2
    obtain ⟨w, hw, hwe⟩ := hz
    have : w = g⁻¹ * z * g := Subtype.ext hwe
    rw [this] at hw
    have h2 : g * (g⁻¹ * z * g) * g⁻¹ ∈ P := hw
    simpa [mul_assoc] using h2
  · intro k hk
    have hmem : ((g⁻¹ * k * g : adjointGroup .G2 K) : ModGL .G2 K) ∈ P'' := by
      refine ⟨g⁻¹ * k * g, ?_, rfl⟩
      show g * (g⁻¹ * k * g) * g⁻¹ ∈ P
      have : g * (g⁻¹ * k * g) * g⁻¹ = k := by group
      rw [this]
      exact hNU hk
    exact hPJ.le hmem

theorem g2_no_simple_normalizing_pSubgroup (K : Type) [Field K] [Finite K] {ℓ : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (h2 : (2 : K) ≠ 0) {U Kb : Subgroup (adjointGroup .G2 K)} [IsSimpleGroup Kb]
    (hKn : ∃ a b : Kb, a * b ≠ b * a) (hU : U ≠ ⊥) (hUp : IsPGroup ℓ U)
    (hKU : Kb ≤ Subgroup.normalizer (U : Set (adjointGroup .G2 K))) : False := by
  classical
  have : Finite (ModGL .G2 K) := finite_modGL
  obtain ⟨g, J, hJ, hk⟩ := exists_conj_le_parabolic_G2 K hU hUp
  obtain ⟨-, -, -, hMP, -, -, hfac, -⟩ := parabolic_root_radical_Levi_factors .G2 K J
  obtain ⟨k0, hk0⟩ : ∃ k0, k0 ∉ J := by
    by_contra h
    push Not at h
    exact hJ (Set.eq_univ_of_forall h)
  obtain ⟨i, hi⟩ : ∃ i : Fin Tag.G2.rank, ∀ j, j ≠ k0 → j = i := by
    fin_cases k0
    · exact ⟨⟨1, by decide⟩, by decide⟩
    · exact ⟨⟨0, by decide⟩, by decide⟩
  have hJi : ∀ j ∈ J, j = i := fun j hj => hi j (fun h => hk0 (h ▸ hj))
  obtain ⟨ρ, hρinj, hρrange⟩ := rankOne_injective_G2 K h2 i
  let ι : Kb →* ModGL .G2 K :=
    (adjointGroup .G2 K).subtype.comp ((MulAut.conj g⁻¹).toMonoidHom.comp Kb.subtype)
  have hιe : ∀ k : Kb, ι k = ((g⁻¹ * (k : adjointGroup .G2 K) * g : adjointGroup .G2 K) : ModGL .G2 K) := by
    intro k
    simp [ι]
  have hι : Function.Injective ι := by
    refine Subtype.val_injective.comp ((MulAut.conj g⁻¹).injective.comp Subtype.val_injective)
  have hιP : ∀ k : Kb, ι k ∈ parabolicSubgroup .G2 K J := by
    intro k
    rw [hιe]
    exact hk k (hKU k.2)
  have hQp : IsPGroup ℓ (parabolicRadical .G2 K J) := by
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨n, -, hcard⟩ := FiniteField.card K ℓ
    have hqcard : Nat.card K = ℓ ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
    refine IsPGroup.of_card (n := (n : ℕ) * (parabolicRadicalRoots .G2 J).ncard) ?_
    rw [card_parabolicRadical, hqcard, ← pow_mul]
  have hD : rankOneGroup K i ≤ ρ.range := by rw [hρrange]; exact le_rfl
  let δ : rankOneGroup K i →* Matrix.SpecialLinearGroup (Fin 2) K :=
    ((MonoidHom.ofInjective hρinj).symm : ρ.range →* _).comp (Subgroup.inclusion hD)
  have hδ : Function.Injective δ :=
    (MonoidHom.ofInjective hρinj).symm.injective.comp (Subgroup.inclusion_injective hD)
  refine false_of_simple_in_semidirect (p := ℓ) (parabolicSubgroup .G2 K J) (parabolicRadical .G2 K J)
    (parabolicLevi .G2 K J) (rankOneGroup K i) hMP ?_ hfac hQp (commutator_parabolicLevi_le K J i hJi)
    hKn ι hι hιP h2 δ hδ
  intro x hx q hq
  exact (Subgroup.mem_normalizer_iff.1
    (parabolicSubgroup_le_normalizer_parabolicRadical J hx) q).1 hq

end CFSG.RankThree.PartOne.K133
