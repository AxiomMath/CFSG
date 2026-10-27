module

public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical
public import CFSG.LocalAnalysis.UniquenessCase.UC22S22a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22p22a_not_two_dvd_ncard {M T K : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hTK : T ≤ normalizer (K : Set G)) : ¬ 2 ∣ (conjSetOf M K).ncard := by
  letI : MulAction ↥M (Subgroup G) :=
    MulAction.compHom (Subgroup G) ((MulAut.conj : G →* MulAut G).comp M.subtype)
  have hsmul : ∀ g : ↥M, g • K = K.map (MulAut.conj (g : G)).toMonoidHom := fun g => rfl
  have horb : MulAction.orbit ↥M K = conjSetOf M K := by
    ext K'
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, g.2, hsmul g⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, (hsmul ⟨g, hg⟩).symm⟩
  have hle : T.subgroupOf M ≤ MulAction.stabilizer ↥M K := by
    intro g hg
    rw [MulAction.mem_stabilizer_iff, hsmul]
    exact mem_normalizer_iff_map_conj_eq.1 (hTK hg)
  have hdvd : (MulAction.stabilizer ↥M K).index ∣ (T.subgroupOf M).index :=
    Subgroup.index_dvd_of_le hle
  have hidx := MulAction.index_stabilizer ↥M K
  rw [horb] at hidx
  rw [← hidx]
  intro h2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd := ((CFSG.ABGLocalTools.isSylowOf_iff (p := 2)).1 hT).2.2
  exact hodd (h2.trans hdvd)

theorem uc22p22a_two_le_of_isSp4 {X : Type} [Group X] {n : ℕ} (h : IsSp4 X n) : 2 ≤ n := by
  obtain ⟨_, hf, _, hne⟩ := CFSG.Blueprint.LieModel.admissible h
  by_contra hlt
  have hn : n = 1 := by omega
  subst hn
  exact hne (by simp)

theorem uc22p22a_two_le_of_isU3 {X : Type} [Group X] {n : ℕ} (h : IsU3 X n) : 2 ≤ n := by
  obtain ⟨_, hf, _, hne⟩ := CFSG.Blueprint.LieModel.admissible h
  by_contra hlt
  have hn : n = 1 := by omega
  subst hn
  exact hne (by simp)

theorem uc22p22a_not_isPowTwo_of_odd {n : ℕ} (hodd : Odd n) (hn : n ≠ 1) : ¬ IsPowTwo n := by
  rintro ⟨k, rfl⟩
  cases k with
  | zero => exact hn (by simp)
  | succ k =>
    have : Even (2 ^ (k + 1)) := (Nat.even_pow.2 ⟨even_two, Nat.succ_ne_zero k⟩)
    exact (Nat.not_even_iff_odd.2 hodd) this

theorem uc22p22a_qs_nontrivial {X : Type} [Group X] (h : CFSG.Open.IsQuasisimple X) : Nontrivial X := by
  haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := h.2
  exact (QuotientGroup.mk_surjective :
    Function.Surjective (QuotientGroup.mk : X → X ⧸ Subgroup.center X)).nontrivial

theorem uc22p22a_qs_not_solvable {X : Type} [Group X] (h : CFSG.Open.IsQuasisimple X) :
    ¬ Group.IsSolvable X := by
  intro hs
  haveI := uc22p22a_qs_nontrivial h
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := X)).ne h.1

theorem uc22p22a_qs_normal {X : Type} [Group X] (h : CFSG.Open.IsQuasisimple X) {W : Subgroup X}
    (hW : W.Normal) : W ≤ Subgroup.center X ∨ W ⊔ Subgroup.center X = ⊤ := by
  haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := h.2
  have hn : (W.map (QuotientGroup.mk' (Subgroup.center X))).Normal :=
    hW.map _ (QuotientGroup.mk'_surjective _)
  rcases hn.eq_bot_or_eq_top with hb | ht
  · left
    intro w hw
    have hmem : (QuotientGroup.mk' (Subgroup.center X)) w ∈
        W.map (QuotientGroup.mk' (Subgroup.center X)) := Subgroup.mem_map_of_mem _ hw
    rw [hb, Subgroup.mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff w).1 hmem
  · right
    have h1 := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center X)) W
    rw [ht, Subgroup.comap_top, QuotientGroup.ker_mk'] at h1
    exact h1.symm

theorem uc22p22a_qs_solvable_normal_le_center {X : Type} [Group X] (h : CFSG.Open.IsQuasisimple X)
    {W : Subgroup X} (hW : W.Normal) (hs : Group.IsSolvable W) : W ≤ Subgroup.center X := by
  rcases uc22p22a_qs_normal h hW with h1 | h2
  · exact h1
  · exfalso
    apply uc22p22a_qs_not_solvable h
    haveI := hW
    haveI := hs
    have hf : Function.Surjective ((QuotientGroup.mk' W).comp (Subgroup.center X).subtype) := by
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective W y
      have hx : x ∈ W ⊔ Subgroup.center X := by rw [h2]; exact Subgroup.mem_top x
      obtain ⟨w, hw, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hx
      refine ⟨⟨z, hz⟩, ?_⟩
      simp [map_mul, (QuotientGroup.eq_one_iff w).2 hw]
    haveI : Group.IsSolvable (X ⧸ W) := Group.isSolvable_of_surjective hf
    exact Group.isSolvable_of_subgroup_quotient W

theorem uc22p22a_isSolvable_preimage_center {A Q : Type} [Group A] [Group Q] (g : A →* Q)
    (hker : Group.IsSolvable g.ker) : Group.IsSolvable ↥((Subgroup.center Q).comap g) := by
  haveI := hker
  have hle : g.ker ≤ (Subgroup.center Q).comap g := fun x hx => by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hx]
    exact Subgroup.one_mem _
  let g₁ : ↥((Subgroup.center Q).comap g) →* ↥(Subgroup.center Q) :=
    (g.comp ((Subgroup.center Q).comap g).subtype).codRestrict _ (fun x => x.2)
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hle) g₁ ?_
  intro x hx
  have hx1 : g x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
  exact ⟨⟨x, MonoidHom.mem_ker.2 hx1⟩, rfl⟩

theorem uc22p22a_ker_solvable {A Q B : Type} [Group A] [Group Q] [Group B] (g : A →* Q)
    (hg : Function.Surjective g) (hgker : Group.IsSolvable g.ker)
    (hQ : CFSG.Open.IsQuasisimple Q) (f : A →* B) (hf : Function.Surjective f)
    (hB : CFSG.Open.IsQuasisimple B) : Group.IsSolvable f.ker := by
  haveI : Group.IsSolvable ↥((Subgroup.center Q).comap g) :=
    uc22p22a_isSolvable_preimage_center g hgker
  have hNn : (f.ker.map g).Normal := (inferInstance : f.ker.Normal).map _ hg
  rcases uc22p22a_qs_normal hQ hNn with h1 | h2
  · have hle : f.ker ≤ (Subgroup.center Q).comap g :=
      fun x hx => h1 (Subgroup.mem_map_of_mem _ hx)
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  · exfalso
    apply uc22p22a_qs_not_solvable hB
    have hsurj : Function.Surjective (f.comp ((Subgroup.center Q).comap g).subtype) := by
      intro y
      obtain ⟨a, rfl⟩ := hf y
      have hx : g a ∈ f.ker.map g ⊔ Subgroup.center Q := by
        rw [h2]
        exact Subgroup.mem_top _
      obtain ⟨w, hw, z, hz, hwz⟩ := Subgroup.mem_sup_of_normal_left.1 hx
      obtain ⟨n, hn, rfl⟩ := hw
      refine ⟨⟨n⁻¹ * a, ?_⟩, ?_⟩
      · show g (n⁻¹ * a) ∈ Subgroup.center Q
        rw [map_mul, map_inv, ← hwz]
        simpa using hz
      · simp [MonoidHom.mem_ker.1 hn]
    exact Group.isSolvable_of_surjective hsurj

theorem uc22p22a_sol_eq {A Q : Type} [Group A] [Group Q] [Finite A] (g : A →* Q)
    (hg : Function.Surjective g) (hgker : Group.IsSolvable g.ker)
    (hQ : CFSG.Open.IsQuasisimple Q) :
    CFSG.solvableRadical A = (Subgroup.center Q).comap g := by
  haveI : Group.IsSolvable ↥((Subgroup.center Q).comap g) :=
    uc22p22a_isSolvable_preimage_center g hgker
  haveI := CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical (G := A)
  apply le_antisymm
  · intro x hx
    have hnorm : ((CFSG.solvableRadical A).map g).Normal :=
      (inferInstance : (CFSG.solvableRadical A).Normal).map _ hg
    haveI : Group.IsSolvable ↥((CFSG.solvableRadical A).map g) :=
      Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective g (CFSG.solvableRadical A))
    exact uc22p22a_qs_solvable_normal_le_center hQ hnorm inferInstance
      (Subgroup.mem_map_of_mem _ hx)
  · exact CFSG.SignalizerFunctorTheorem.Nonsolvable.le_solvableRadical
      (Subgroup.Normal.comap inferInstance _) inferInstance

theorem uc22p22a_equiv_of_sol_eq {A Q : Type} [Group A] [Group Q] (g : A →* Q)
    (hg : Function.Surjective g)
    (hsol : CFSG.solvableRadical A = (Subgroup.center Q).comap g) :
    Nonempty ((A ⧸ CFSG.solvableRadical A) ≃* (Q ⧸ Subgroup.center Q)) := by
  have hh : Function.Surjective ((QuotientGroup.mk' (Subgroup.center Q)).comp g) :=
    (QuotientGroup.mk'_surjective _).comp hg
  have hker : ((QuotientGroup.mk' (Subgroup.center Q)).comp g).ker = CFSG.solvableRadical A := by
    rw [hsol, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hh)⟩

theorem uc22p22a_key {A Q B : Type} [Group A] [Group Q] [Group B] [Finite A] (g : A →* Q)
    (hg : Function.Surjective g) (hgker : Group.IsSolvable g.ker)
    (hQ : CFSG.Open.IsQuasisimple Q) (f : A →* B) (hf : Function.Surjective f)
    (hB : CFSG.Open.IsQuasisimple B) :
    Nonempty ((Q ⧸ Subgroup.center Q) ≃* (B ⧸ Subgroup.center B)) ∧
      Nonempty ((A ⧸ CFSG.solvableRadical A) ≃* (B ⧸ Subgroup.center B)) := by
  have hfker := uc22p22a_ker_solvable g hg hgker hQ f hf hB
  obtain ⟨e₁⟩ := uc22p22a_equiv_of_sol_eq g hg (uc22p22a_sol_eq g hg hgker hQ)
  obtain ⟨e₂⟩ := uc22p22a_equiv_of_sol_eq f hf (uc22p22a_sol_eq f hf hfker hB)
  exact ⟨⟨e₁.symm.trans e₂⟩, ⟨e₂⟩⟩

theorem uc22p22a_le_of_isSubnormal {A B : Subgroup G} (h : CFSG.Open.IsSubnormal A B) : A ≤ B := by
  induction h with
  | refl => exact le_rfl
  | step hHM _ _ ih => exact hHM.trans ih

theorem uc22p22a_exists_surj (M V K : Subgroup G) (hKM : K ≤ M) :
    ∃ f : ↥K →* ↥(mbarImage M V K), Function.Surjective f := by
  let φ : ↥K →* MBar M V :=
    (QuotientGroup.mk' (kerAct M V).normalCore).comp (Subgroup.inclusion hKM)
  have hmem : ∀ x : ↥K, φ x ∈ mbarImage M V K := fun x => ⟨Subgroup.inclusion hKM x, x.2, rfl⟩
  refine ⟨φ.codRestrict _ hmem, fun y => ?_⟩
  obtain ⟨z, hz, hzy⟩ := y.2
  exact ⟨⟨(z : G), hz⟩, Subtype.ext hzy⟩

theorem uc22p22a_data (D : Data G) {Ch : Choice2011 G} (c : Ctx22b D Ch) {K : Subgroup G}
    (hKC : K ∈ calC D.M) (hB : CFSG.Open.IsQuasisimple ↥(mbarImage D.M c.V K)) :
    Nonempty ((Bar2 K ⧸ Subgroup.center (Bar2 K)) ≃*
      (↥(mbarImage D.M c.V K) ⧸ Subgroup.center ↥(mbarImage D.M c.V K))) ∧
    Nonempty (BarInf K ≃*
      (↥(mbarImage D.M c.V K) ⧸ Subgroup.center ↥(mbarImage D.M c.V K))) := by
  have hKM : K ≤ D.M := uc22p22a_le_of_isSubnormal hKC.1
  obtain ⟨f, hf⟩ := uc22p22a_exists_surj D.M c.V K hKM
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent ↥(CFSG.pCore 2 ↥K) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).isNilpotent
  have hgker : Group.IsSolvable (QuotientGroup.mk' (CFSG.pCore 2 ↥K)).ker := by
    rw [QuotientGroup.ker_mk']
    infer_instance
  exact uc22p22a_key (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (QuotientGroup.mk'_surjective _)
    hgker hKC.2.2 f hf hB

theorem uc22p22a_shape_su3 (D : Data G) {Ch : Choice2011 G} (c : Ctx22b D Ch) {K : Subgroup G}
    (hKC : K ∈ calC D.M) {n : ℕ} (hsu : IsSU3 ↥(mbarImage D.M c.V K) n) :
    IsSU3 (Bar2 K) n := by
  obtain ⟨⟨e⟩, -⟩ := uc22p22a_data D c hKC hsu.1
  exact ⟨hKC.2.2, CFSG.Blueprint.LieModel.of_mulEquiv e.symm hsu.2⟩

theorem uc22p22a_center_eq_bot {X : Type} [Group X] [IsSimpleGroup X]
    (hn : ∃ a b : X, a * b ≠ b * a) : Subgroup.center X = ⊥ := by
  rcases (inferInstance : (Subgroup.center X).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hn
    have ha : a ∈ Subgroup.center X := by rw [h]; exact Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.1 ha b).symm

theorem uc22p22a_isQuasisimple_of_simple {X : Type} [Group X] [IsSimpleGroup X]
    (hn : ∃ a b : X, a * b ≠ b * a) : CFSG.Open.IsQuasisimple X := by
  have hc := uc22p22a_center_eq_bot hn
  refine ⟨?_, ?_⟩
  · rcases (inferInstance : (commutator X).Normal).eq_bot_or_eq_top with h | h
    · exfalso
      have h1 := (commutator_eq_bot_iff_center_eq_top X).1 h
      rw [hc] at h1
      exact bot_ne_top h1
    · exact h
  · exact MulEquiv.isSimpleGroup
      ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot)

theorem uc22p22a_sp4_simple (X : Type) [Group X] (n : ℕ) (hsp : IsSp4 X n) :
    IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a := by
  have hn2 := uc22p22a_two_le_of_isSp4 hsp
  obtain ⟨-, F, hFf, hFfin, hF, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num : (2 : ℕ) ≠ 0) hsp
  have hF4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hsimpleP : IsSimpleGroup (StatedProj (StatedSp 2 F)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F 2 (by omega)
      (Or.inl (Or.inr hF4))
  have hperfP : Group.IsPerfect (StatedProj (StatedSp 2 F)) := by
    haveI : Fintype F := Fintype.ofFinite F
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hF4)
    exact CFSG.ClassicalGroups.Symplectic.symplectic_projective_perfect 2 F (Or.inl ⟨t, ht⟩)
  haveI hsimple : IsSimpleGroup X := e.isSimpleGroup
  haveI : Group.IsPerfect X := by
    have := hperfP
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  refine ⟨hsimple, ?_⟩
  by_contra hcon
  push Not at hcon
  exact Group.IsPerfect.not_isMulCommutative X ⟨⟨fun a b => hcon a b⟩⟩

theorem uc22p22a_shape_sp4 (D : Data G) {Ch : Choice2011 G} (c : Ctx22b D Ch) {K : Subgroup G}
    (hKC : K ∈ calC D.M) {n : ℕ} (hsp : IsSp4 ↥(mbarImage D.M c.V K) n) :
    IsSp4 (BarInf K) n := by
  obtain ⟨hsimple, hnab⟩ := uc22p22a_sp4_simple _ n hsp
  haveI := hsimple
  obtain ⟨-, ⟨e⟩⟩ := uc22p22a_data D c hKC (uc22p22a_isQuasisimple_of_simple hnab)
  have hc : Subgroup.center ↥(mbarImage D.M c.V K) = ⊥ := uc22p22a_center_eq_bot hnab
  exact CFSG.Blueprint.LieModel.of_mulEquiv
    (e.trans ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot)).symm hsp

end CFSG.LocalAnalysis.UniquenessCase.UC22
