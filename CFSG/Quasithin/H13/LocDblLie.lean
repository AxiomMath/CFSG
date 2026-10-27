module

public import CFSG.Quasithin.H13.LocDblCriterion
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListD4
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListF4
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListG2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSp4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6TitsLattice
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6A312Over

public section

namespace CFSG.Quasithin.H13.LocDbl

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.QuasithinUnique.Setup.X6
open CFSG.QuasithinUnique.Vol2Native.A312L

section OneSylow

variable {A : Type} [Group A] [Finite A]

omit [Finite A] in
theorem noIsoDouble_of_subsingleton {Y : Subgroup A} (h : (cComp Y).Subsingleton) :
    NoIsoDouble Y := fun _ hU _ hV _ => h hU hV

omit [Finite A] in
theorem map_map_symm_self (e : A ≃* A) (Y : Subgroup A) :
    (Y.map e.symm.toMonoidHom).map e.toMonoidHom = Y := by
  rw [Subgroup.map_map, show e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id A by
    ext; simp, Subgroup.map_id]

omit [Finite A] in
theorem map_symm_map_self (e : A ≃* A) (Y : Subgroup A) :
    (Y.map e.toMonoidHom).map e.symm.toMonoidHom = Y := by
  rw [Subgroup.map_map, show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id A by
    ext; simp, Subgroup.map_id]

theorem sylowNoDouble_of_sylow {U : Subgroup A} (hU : IsSylowTwoOf U ⊤)
    (h : ∀ Y : Subgroup A, U ≤ Y → Y ≠ ⊤ → NoIsoDouble Y) : SylowNoDouble A := by
  intro R hR Y hRY hY
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf hU hR
  set e : A ≃* A := MulAut.conj g with he
  have hY' : Y.map e.symm.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hY
    have := congrArg (Subgroup.map e.toMonoidHom) htop
    rwa [map_map_symm_self, Subgroup.map_top_of_surjective _ e.surjective] at this
  have hUY : U ≤ Y.map e.symm.toMonoidHom := by
    rw [← map_symm_map_self e U]
    refine Subgroup.map_mono ?_
    rw [show U.map e.toMonoidHom = R from hg]
    exact hRY
  have := NoIsoDouble.map e (h _ hUY hY')
  rwa [map_map_symm_self] at this

theorem sylowNoDouble_of_solvable {U : Subgroup A} (hU : IsSylowTwoOf U ⊤)
    (h : ∀ M : Subgroup A, U ≤ M → M ≠ ⊤ → Group.IsSolvable ↥M) : SylowNoDouble A :=
  sylowNoDouble_of_sylow hU fun Y hUY hY U' hU' _ _ _ => by
    exfalso
    have := h Y hUY hY
    exact not_isSolvable_of_mem_cComp hU'
      (Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (le_of_mem_cComp hU' : U' ≤ Y)) (Subgroup.inclusion_injective _))

end OneSylow

section Rank2

variable {S : Type} [Group S] [Finite S]

@[expose] def SimpleLevi (P : Subgroup S) : Prop :=
  perfectCore P = ⊥ ∨ ∃ (T : Type) (_ : Group T) (_ : IsSimpleGroup T), (∃ a b : T, a * b ≠ b * a) ∧
    ∃ f : ↥(perfectCore P) →* T, Function.Surjective f ∧ Group.IsSolvable f.ker

theorem cComp_subsingleton_of_residual {U : Subgroup S} {P : Fin 2 → Subgroup S}
    (hP : ResidualOvergroupsAt S U P) (hL : ∀ j, SimpleLevi (P j)) {Y : Subgroup S}
    (hUY : U ≤ Y) (hY : Y ≠ ⊤) : (cComp Y).Subsingleton := by
  by_cases hs : Group.IsSolvable ↥Y
  · intro L₁ h₁ _ _
    exfalso
    exact not_isSolvable_of_mem_cComp h₁
      (Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (le_of_mem_cComp h₁ : L₁ ≤ Y)) (Subgroup.inclusion_injective _))
  obtain ⟨j, -, hd⟩ := hP.2.2.2.2.1 Y hUY hY hs
  have hYD : perfectCore Y = perfectCore (P j) := by
    rw [← dInf_eq_perfectCore, ← dInf_eq_perfectCore, hd]
  rcases hL j with h0 | ⟨T, _, _, hT, f, hf, hker⟩
  · exact absurd ((isSolvable_iff_perfectCore_eq_bot _).mpr (hYD.trans h0)) hs
  have hperf : ⁅(⊤ : Subgroup ↥(perfectCore (P j))), (⊤ : Subgroup ↥(perfectCore (P j)))⁆ =
      ⊤ :=
    Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr (perfectCore_perfect (P j)))
  have key : ∀ L ∈ cComp Y, L = perfectCore (P j) := by
    intro L hL
    have hLD : L ≤ perfectCore Y :=
      le_perfectCore_of_perfect (le_of_mem_cComp hL) (perfect_of_mem_cComp hL)
    have hLD' : L ∈ cComp (perfectCore Y) := cComp_mem_of_le hL hLD (perfectCore_le Y)
    rw [hYD] at hLD hLD'
    have htop := cComp_top_eq_of_hom hT hperf f hf hker _ (subgroupOf_mem_cComp hLD')
    exact le_antisymm hLD (Subgroup.subgroupOf_eq_top.mp htop)
  intro L₁ h₁ L₂ h₂
  rw [key L₁ h₁, key L₂ h₂]

theorem simpleLevi_of_leviData {P : Subgroup S} (h : LeviData P) : SimpleLevi P := by
  rcases h with h | ⟨K, _, _, _, n, hn, hn2, g, hg, hker⟩
  · exact Or.inl h
  · have hK4 : ∃ s : Finset K, s.card = 4 := by
      refine exists_finset_card_four ?_
      rw [hn]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hsolv : Group.IsSolvable g.ker := by
      have := hker.isNilpotent
      infer_instance
    exact Or.inr ⟨_, inferInstance, sl2_isSimple hK4, sl2_nonabelian hK4, g, hg, hsolv⟩

theorem simpleLevi_of_leviDataSz
    {f : ℕ} {P : Subgroup S} (h : LeviDataSz f P) :
    SimpleLevi P := by
  obtain ⟨a, K, _, _, ha, hfa, hK, g, hg, hker⟩ := h
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hK
  obtain ⟨-, -, hsimple⟩ := CFSG.LieType.Ree.suzuki_simple ha hK'
  have hnab : ∃ x y : CFSG.Blueprint.suzukiGroup a K, x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    have : IsMulCommutative (CFSG.Blueprint.suzukiGroup a K) := ⟨⟨hcon⟩⟩
    have : Group.IsPerfect (CFSG.Blueprint.suzukiGroup a K) :=
      (CFSG.LieType.Ree.suzuki_perfect ha hK').2
    exact Group.IsPerfect.not_isMulCommutative (CFSG.Blueprint.suzukiGroup a K) ‹_›
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsolv : Group.IsSolvable g.ker := by
    have := hker.isNilpotent
    infer_instance
  exact Or.inr ⟨_, inferInstance, hsimple, hnab, g, hg, hsolv⟩

theorem sylowNoDouble_of_rank2_levi {U : Subgroup S} {P : Fin 2 → Subgroup S}
    (hU : IsSylowTwoOf U ⊤) (hP : ResidualOvergroupsAt S U P) {K : Type} [Field K] [Finite K]
    [CharP K 2] {f : ℕ} (hf : Nat.card K = 2 ^ f) (hf2 : 2 ≤ f)
    (g : ∀ j, ↥(perfectCore (P j)) →* Matrix.SpecialLinearGroup (Fin 2) K)
    (hg : ∀ j, Function.Surjective (g j)) (hker : ∀ j, IsPGroup 2 (g j).ker) :
    SylowNoDouble S :=
  sylowNoDouble_of_sylow hU fun _ hUY hY => noIsoDouble_of_subsingleton
    (cComp_subsingleton_of_residual hP
      (fun j => simpleLevi_of_leviData (Or.inr ⟨K, inferInstance, inferInstance, inferInstance, f,
        hf, hf2, g j, hg j, hker j⟩)) hUY hY)

end Rank2

section Families

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a

theorem sylowNoDouble_projSp4 {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hf : Nat.card K = 2 ^ f) (hf2 : 2 ≤ f) :
    SylowNoDouble
      (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 K)) := by
  have hK : ∃ k : ℕ, Nat.card K = 2 ^ k := ⟨f, hf⟩
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hf]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have hres : ResidualOvergroupsAt
      (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 K))
      (projUnipotent 2 K)
      (fun j : Fin 2 => (Q2 K j).map (proj 2 K)) := symplectic_two_residualOvergroupsAt hK
  obtain ⟨P, hP⟩ := exists_sylow_projUnipotent (K := K) 2 (r := 2) (by norm_num)
  have hU : IsSylowTwoOf (projUnipotent 2 K) ⊤ :=
    hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  have hinj : ∀ j : Fin 2, ∀ x ∈ perfectCore (Q2 K j), ∀ y ∈ perfectCore (Q2 K j),
      proj 2 K x = proj 2 K y → x = y := fun j x _ y _ h => proj_injective_charTwo h
  let eN : ∀ j : Fin 2, ↥(perfectCore (Q2 K j)) ≃* ↥(perfectCore ((Q2 K j).map (proj 2 K))) :=
    fun j => perfectCoreMapEquiv (proj 2 K) (Q2 K j) (hinj j)
  refine sylowNoDouble_of_rank2_levi hU hres hf hf2
    (fun j => (blkN j).comp (eN j).symm.toMonoidHom)
    (fun j => (blkN_surjective hK4 j).comp (eN j).symm.surjective) fun j z => ?_
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := blkN_ker_isPGroup hK j ⟨(eN j).symm z.1, z.2⟩
  have h1 : ((eN j).symm z.1) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  refine ⟨k, Subtype.ext ?_⟩
  show z.1 ^ 2 ^ k = 1
  have : (eN j).symm (z.1 ^ 2 ^ k) = 1 := by rw [map_pow]; exact h1
  exact (map_eq_one_iff _ (eN j).symm.injective).mp this

end Families

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley in
theorem sylowNoDouble_G2
    {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf2 : 2 ≤ f) : SylowNoDouble ↥(adjointGroup Tag.G2 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hU₀ : IsSylowTwoOf
      ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)) ⊤ :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_subgroupOf_top (isSylowTwoOf_iff_isSylowOf.2
      (unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := K) 2).1)
  choose g hg hker using fun j : Fin 2 =>
    exists_levi_hom_adjoint (τ := Tag.G2) (K := K) hK hf2 (g2Index j)
  exact sylowNoDouble_of_rank2_levi hU₀ G2_residualOvergroupsAt hK hf2 g hg hker

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley in
theorem sylowNoDouble_D4
    {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f) (σ : K ≃+* K)
    (hK : Nat.card K = (2 ^ f) ^ 3) :
    SylowNoDouble ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨PU, hPU⟩ := (exceptional_fixed_Sylow_opposition TwistTag.D4 K 2 σ w₀ hw₀).1
  have hUC : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  have hUsyl : IsSylowTwoOf (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  have hU₀ := CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_subgroupOf_top hUsyl
  exact sylowNoDouble_of_sylow hU₀ fun _ hUY hY => noIsoDouble_of_subsingleton
    (cComp_subsingleton_of_residual (triality_residualOvergroupsAt σ)
      (fun j => simpleLevi_of_leviData (fixed_leviData σ (d4Index j) hUsyl.2.1)) hUY hY)

open CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Ree.LargeReeInvolution in
theorem sylowNoDouble_F4
    {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) : SylowNoDouble ↥(F4.reeGamma K a) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL F4.tag K) := finite_modGL
  have hchar : CharP K 2 := inferInstanceAs (CharP K F4.prime)
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem F4.tag).length
  obtain ⟨PU, hPU⟩ := (large_Ree_Sylow_opposition F4 a K w₀ hw₀).1
  have hUC : F4.reeFixedPosUnipotent K a ≤ F4.reeGamma K a := reeFixedPosUnipotent_le_reeGamma
  have hUsyl : IsSylowTwoOf (F4.reeFixedPosUnipotent K a) (F4.reeGamma K a) := by
    refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  have hU₀ := CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_subgroupOf_top hUsyl
  have hUp : IsPGroup 2 ↥(F4.reeFixedPosUnipotent K a) := hUsyl.2.1
  obtain ⟨⟨h0eq, -, -⟩, ⟨h1eq, -, -⟩⟩ :=
    large_Ree_opposite_simple_blocks_generate_rank_one_model ha hK
  refine sylowNoDouble_of_sylow hU₀ fun _ hUY hY => noIsoDouble_of_subsingleton
    (cComp_subsingleton_of_residual (large_Ree_residualOvergroupsAt hK) (fun j => ?_) hUY hY)
  have hcases : ∀ i : Fin F4.fixedOrbitCount, i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ := by
    intro i
    rcases i with ⟨i, hi⟩
    have hi2 : i < 2 := hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hcases (f4Index j) with hj | hj
  · have : IsSimpleGroup ↥(rankOneGroupOne K a) := (isSimpleGroup_rankOneGroupOne ha hK).1
    obtain ⟨g, hg, hk⟩ := ree_levi_hom (K := K) (a := a) hUp (f4Index j)
      (M := rankOneGroupOne K a) (by rw [hj]; exact h0eq)
      (isSimpleGroup_rankOneGroupOne ha hK).2
    let e : ↥(rankOneGroupOne K a) ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
      (rankOneEquivSL K a hK).symm
    refine simpleLevi_of_leviData (Or.inr ⟨K, inferInstance, inferInstance, hchar, 2 * a + 1, hK,
      by omega, e.toMonoidHom.comp g, e.surjective.comp hg, ?_⟩)
    have hkerEq : (e.toMonoidHom.comp g).ker = g.ker := by
      ext x
      simp only [MonoidHom.mem_ker]
      exact MulEquiv.map_eq_one_iff e
    rw [hkerEq]
    exact hk
  · have : IsSimpleGroup ↥(rankOneGroupTwo K a) := (isSimpleGroup_rankOneGroupTwo ha hK).1
    obtain ⟨g, hg, hk⟩ := ree_levi_hom (K := K) (a := a) hUp (f4Index j)
      (M := rankOneGroupTwo K a) (by rw [hj]; exact h1eq)
      (isSimpleGroup_rankOneGroupTwo ha hK).2
    let e : ↥(rankOneGroupTwo K a) ≃* CFSG.Blueprint.suzukiGroup a K :=
      rankOneEquivSuzuki K a ha hK
    refine simpleLevi_of_leviDataSz (f := 2 * a + 1) ⟨a, K, inferInstance, inferInstance, ha, rfl,
      hK, e.toMonoidHom.comp g, e.surjective.comp hg, ?_⟩
    have hkerEq : (e.toMonoidHom.comp g).ker = g.ker := by
      ext x
      simp only [MonoidHom.mem_ker]
      exact MulEquiv.map_eq_one_iff e
    rw [hkerEq]
    exact hk

theorem sylowNoDouble_of_bender {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hB : CFSG.Open.fusionIsBenderGroup X) : SylowNoDouble X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q⟩ := (Sylow.nonempty : Nonempty (Sylow 2 X))
  exact sylowNoDouble_of_solvable (CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow Q)
    fun M hQM hM => CFSG.QuasithinUnique.Unc25G2.A312Sub.bender_overgroups hB Q hQM hM

theorem sylowNoDouble_suzuki {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {f : ℕ}
    (hX : CFSG.Blueprint.SuzukiModel X 2 f) : SylowNoDouble X := by
  obtain ⟨a, ha, ⟨e⟩⟩ := CFSG.LieType.Simplicity.exists_mulEquiv_suzukiMatrixGroup_of_suzukiModel hX
  exact sylowNoDouble_of_bender
    (Or.inr (Or.inr ⟨a, ha, ⟨e.trans (CFSG.ShultStronglyClosedTI.suzukiCoverNativeEquiv a).symm⟩⟩))

theorem sylowNoDouble_tits
    {X : Type} [Group X] [Finite X]
    (hX : CFSG.Blueprint.ReeTitsModel X .Tits 2 1) : SylowNoDouble X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀⟩ := (Sylow.nonempty : Nonempty (Sylow 2 X))
  have hT := CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P₀
  generalize (P₀ : Subgroup X) = U at hT
  obtain ⟨H, N, -, -, -, -, -, hlat, hHs, hNs⟩ :=
    CFSG.QuasithinUnique.Setup.X6.titsSylowOvergroupLattice X hX U hT
  refine sylowNoDouble_of_solvable hT fun M hUM hMtop => ?_
  rcases hlat M hUM with rfl | rfl | rfl | rfl
  · have := hT.2.1.isNilpotent
    infer_instance
  · exact hHs
  · exact hNs
  · exact absurd rfl hMtop


end CFSG.Quasithin.H13.LocDbl
