module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Infrastructure
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.lemma_3_2_a
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.lemma_3_2_b
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.lemma_3_3

namespace CFSG
end CFSG
open CFSG

open scoped FixedPoints TensorProduct Pointwise

universe uG uF uV

abbrev CFSG.Theorem35IndHyp {G : Type uG} [Group G] [Finite G] {F : Type uF} [Field F]
    (K : Subgroup G) : Prop :=
  ∀ {V' : Type uV} [AddCommGroup V'] [Module F V']
    {G' : Type uG} [Group G'] [Finite G'] (K' R' : Subgroup G')
    (ρ' : Representation F G' V'),
    Nat.card K' < Nat.card K →
    IsFrobeniusGroupWithKernelComplement K' R' →
    Group.IsSolvable K' →
    IsCyclic R' →
    Nat.Prime (Nat.card R') →
    (ringChar F = 0 ∨
      (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card G'))) →
    Module.rank F ↥(ρ'.fixedSubspace R') = 1 →
    ⁅K', K'⁆ ≤ ρ'.centralizerIn K'

theorem CFSG.theorem_3_5_quotient_step {G : Type uG} [Group G] [Finite G] {F : Type uF}
    [Field F] {V : Type uV} [AddCommGroup V] [Module F V]
    (K R : Subgroup G) (ρ : Representation F G V)
    (hind : Theorem35IndHyp.{uG, uF, uV} (F := F) K)
    (hfrob : IsFrobeniusGroupWithKernelComplement K R) (hsolvK : Group.IsSolvable K)
    (hR_cyclic : IsCyclic R) (hR_prime : Nat.Prime (Nat.card R))
    (hchar : ringChar F = 0 ∨
      (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card G)))
    (hfixR : Module.rank F ↥(ρ.fixedSubspace R) = 1)
    (hker_ne_bot : ρ.ker ≠ ⊥) (hKnle : ¬ K ≤ ρ.ker) :
    ⁅K, K⁆ ≤ ρ.centralizerIn K := by
  let N : Subgroup G := ρ.ker
  have hN_le_K : N ≤ K :=
    lemma_3_2_a (K := K) (R := R) (N := N) hfrob hsolvK hKnle
  let : N.Normal := inferInstance
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let : Representation.IsTrivial (ρ.comp N.subtype) :=
    isTrivialCompSubtypeOfLeKer (ρ := ρ) (N := N) (by
      intro x hx
      exact hx)
  let : Group.IsSolvable ↥K := hsolvK
  have hsolv_map : Group.IsSolvable ↥(K.map q) :=
    Group.isSolvable_of_surjective (f := q.subgroupMap K) (MonoidHom.subgroupMap_surjective q K)
  let : IsCyclic ↥R := hR_cyclic
  have hR_map_cyclic : IsCyclic ↥(R.map q) :=
    isCyclic_of_surjective (f := q.subgroupMap R) (MonoidHom.subgroupMap_surjective q R)
  have hcard_quot_dvd : Nat.card (G ⧸ N) ∣ Nat.card G := by
    exact ⟨Nat.card N, by
      simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := G) (s := N))⟩
  have hquot_fix :
      Module.rank F ↥((Representation.ofQuotient ρ N).fixedSubspace (R.map q)) = 1 := by
    rw [fixedSubspace_map_mk'_ofQuotient_eq (ρ := ρ) (N := N) (R := R)]
    exact hfixR
  have hquot :=
    hind (G' := G ⧸ N) (K.map q) (R.map q) (Representation.ofQuotient ρ N)
      (natCard_map_mk'_lt_of_ne_bot K N hN_le_K hker_ne_bot)
      (lemma_3_2_b (K := K) (R := R) (N := N) hfrob hsolvK hKnle)
      hsolv_map
      hR_map_cyclic
      (prime_card_map_mk'_of_le_isComplement' K R N hN_le_K hfrob.isComplement' hR_prime)
      (hchar_of_card_dvd (G := G) (F := F) hchar hcard_quot_dvd)
      hquot_fix
  exact
    commutator_le_centralizerIn_of_map_le_centralizerIn_ofQuotient
      (N := N) (K := K) (R := K) (ρ := ρ) hfrob.normal hquot


set_option backward.isDefEq.respectTransparency false in
theorem CFSG.theorem_3_5_exists_irreducible_counterexample
    {G : Type uG} [Group G] [Finite G] {F : Type uF} [Field F] {V : Type uV}
    [AddCommGroup V] [Module F V]
    (K R : Subgroup G) (ρ : Representation F G V)
    [IsSemisimpleModule (MonoidAlgebra F G) ρ.asModule]
    (hfrob : IsFrobeniusGroupWithKernelComplement K R)
    (hchar : ringChar F = 0 ∨
      (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card G)))
    (hbad : ¬ ⁅K, K⁆ ≤ ρ.centralizerIn K) :
    ∃ m : Submodule (MonoidAlgebra F G) ρ.asModule,
      IsSimpleModule (MonoidAlgebra F G) m ∧
      let ρm := (Subrepresentation.ofSubmodule' m).toRepresentation
      ρm.fixedSubspace R ≠ ⊥ ∧
      ¬ ⁅K, K⁆ ≤ ρm.ker := by
  let : K.Normal := hfrob.normal
  have hbad_ker : ¬ ⁅K, K⁆ ≤ ρ.ker := by
    intro hker
    exact hbad ((commutator_le_centralizerIn_iff_le_ker (ρ := ρ) (R := K) (K := K)).2 hker)
  obtain ⟨m, hm, hm_bad⟩ :=
    exists_simple_submodule_nontrivial_of_not_le_ker (ρ := ρ) (H := ⁅K, K⁆) hbad_ker
  have hm_fix :
      (Subrepresentation.ofSubmodule' m).toRepresentation.fixedSubspace R ≠ ⊥ :=
    lemma_3_3 K R (Subrepresentation.ofSubmodule' m).toRepresentation hfrob
      (hchar_of_card_dvd (G := G) (F := F) hchar (Subgroup.card_subgroup_dvd_card K))
      (by
        intro hKker
        exact hm_bad (le_trans (Subgroup.commutator_le_right (H₁ := K) (H₂ := K)) hKker))
  exact ⟨m, hm, hm_fix, hm_bad⟩

theorem CFSG.theorem_3_5_fixedSubspace_rank_one_of_nonzero
    {G : Type uG} [Group G] [Finite G] {F : Type uF} [Field F] {V : Type uV}
    [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (R : Subgroup G)
    {m : Submodule (MonoidAlgebra F G) ρ.asModule}
    (hfixR : Module.rank F ↥(ρ.fixedSubspace R) = 1)
    (hfixm :
      (Subrepresentation.ofSubmodule' m).toRepresentation.fixedSubspace R ≠ ⊥) :
    Module.rank F ↥((Subrepresentation.ofSubmodule' m).toRepresentation.fixedSubspace R) = 1 := by
  let S : Submodule F m := (Subrepresentation.ofSubmodule' m).toRepresentation.fixedSubspace R
  let i : S →ₗ[F] ↥(ρ.fixedSubspace R) := {
    toFun := fun v => ⟨v.1.1, by
      change v.1.1 ∈ ρ.fixedSubspace R
      have hv_mem : v.1 ∈ S := v.2
      change v.1 ∈ (Subrepresentation.ofSubmodule' m).toRepresentation.fixedSubspace R at hv_mem
      change ∀ r : R, (Subrepresentation.ofSubmodule' m).toRepresentation r v.1 = v.1 at hv_mem
      change ∀ r : R, ρ r v.1.1 = v.1.1
      intro r
      exact congrArg Subtype.val (hv_mem r)⟩
    map_add' := by
      intro v w
      ext
      rfl
    map_smul' := by
      intro a v
      ext
      rfl
  }
  have hi_inj : Function.Injective i := by
    intro v w hEq
    have hEqV : v.1.1 = w.1.1 := by
      have hEq' := congrArg (fun x : ↥(ρ.fixedSubspace R) => (x : V)) hEq
      change v.1.1 = w.1.1 at hEq'
      exact hEq'
    exact Subtype.ext <| Subtype.ext hEqV
  let : FiniteDimensional F ↥(ρ.fixedSubspace R) := FiniteDimensional.of_rank_eq_one hfixR
  have hfin_fix : Module.finrank F ↥(ρ.fixedSubspace R) = 1 :=
    (Module.rank_eq_one_iff_finrank_eq_one (R := F) (M := ↥(ρ.fixedSubspace R))).mp hfixR
  let : FiniteDimensional F S := FiniteDimensional.of_injective i hi_inj
  have hfin_le : Module.finrank F S ≤ 1 := by
    calc
      Module.finrank F S ≤ Module.finrank F ↥(ρ.fixedSubspace R) :=
        LinearMap.finrank_le_finrank_of_injective (f := i) hi_inj
      _ = 1 := hfin_fix
  have hfin_pos : 0 < Module.finrank F S := by
    refine Nat.pos_of_ne_zero ?_
    intro hzero
    apply hfixm
    change S = ⊥
    exact (Submodule.finrank_eq_zero).mp hzero
  have hfin_S : Module.finrank F S = 1 := by
    omega
  change Module.rank F S = 1
  exact (Module.rank_eq_one_iff_finrank_eq_one (R := F) (M := S)).2 hfin_S

set_option backward.isDefEq.respectTransparency false in
theorem CFSG.theorem_3_5_faithful_reduction
    {G : Type uG} [Group G] [Finite G] {F : Type uF} [Field F] {V : Type uV}
    [AddCommGroup V] [Module F V]
    (K R : Subgroup G) (ρ : Representation F G V)
    (hind :
      ∀ {W : Type uV} [AddCommGroup W] [Module F W]
        {G' : Type uG} [Group G'] [Finite G'] (K' R' : Subgroup G')
        (ρ' : Representation F G' W),
        Nat.card K' < Nat.card K →
        IsFrobeniusGroupWithKernelComplement K' R' →
        Group.IsSolvable K' →
        IsCyclic R' →
        Nat.Prime (Nat.card R') →
        (ringChar F = 0 ∨
          (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card G'))) →
        Module.rank F ↥(ρ'.fixedSubspace R') = 1 →
        ⁅K', K'⁆ ≤ ρ'.centralizerIn K')
    [IsSemisimpleModule (MonoidAlgebra F G) ρ.asModule]
    (hfrob : IsFrobeniusGroupWithKernelComplement K R) (hsolvK : Group.IsSolvable K)
    (hR_cyclic : IsCyclic R) (hR_prime : Nat.Prime (Nat.card R))
    (hchar : ringChar F = 0 ∨
      (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card G)))
    (hfixR : Module.rank F ↥(ρ.fixedSubspace R) = 1)
    (hbad : ¬ ⁅K, K⁆ ≤ ρ.centralizerIn K) :
    ∃ m : Submodule (MonoidAlgebra F G) ρ.asModule,
      IsSimpleModule (MonoidAlgebra F G) m ∧
      let ρm := (Subrepresentation.ofSubmodule' m).toRepresentation
      Module.rank F ↥(ρm.fixedSubspace R) = 1 ∧
      ρm.ker = ⊥ ∧
      ¬ ⁅K, K⁆ ≤ ρm.ker := by
  let : K.Normal := hfrob.normal
  obtain ⟨m, hm_simple, hm_fix, hm_bad⟩ :=
    theorem_3_5_exists_irreducible_counterexample K R ρ hfrob hchar hbad
  let ρm := (Subrepresentation.ofSubmodule' m).toRepresentation
  have hfixm_rank :
      Module.rank F ↥(ρm.fixedSubspace R) = 1 :=
    theorem_3_5_fixedSubspace_rank_one_of_nonzero (ρ := ρ) (R := R) hfixR hm_fix
  by_cases hker_bot : ρm.ker = ⊥
  · exact ⟨m, hm_simple, hfixm_rank, hker_bot, hm_bad⟩
  · have hKnle : ¬ K ≤ ρm.ker := by
      intro hKle
      exact hm_bad (le_trans (Subgroup.commutator_le_right (H₁ := K) (H₂ := K)) hKle)
    have hquot :=
      theorem_3_5_quotient_step K R ρm hind hfrob hsolvK hR_cyclic hR_prime hchar
        hfixm_rank hker_bot hKnle
    have hquot_ker : ⁅K, K⁆ ≤ ρm.ker := by
      intro z hz
      exact (hquot hz).2
    exact False.elim (hm_bad hquot_ker)

theorem CFSG.theorem_3_5_proper_invariant_subgroups_abelian
    {G : Type uG} [Group G] [Finite G] {F : Type uF} [Field F] {V : Type uV}
    [AddCommGroup V] [Module F V]
    (K R : Subgroup G) (ρ : Representation F G V)
    (hind : Theorem35IndHyp.{uG, uF, uV} (F := F) K)
    (hfrob : IsFrobeniusGroupWithKernelComplement K R) (hsolvK : Group.IsSolvable K)
    (hR_cyclic : IsCyclic R) (hR_prime : Nat.Prime (Nat.card R))
    (hchar : ringChar F = 0 ∨
      (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card G)))
    (hfixR : Module.rank F ↥(ρ.fixedSubspace R) = 1)
    (hker_bot : ρ.ker = ⊥)
    (N : Subgroup G) (hN_lt : N < K)
    (hRinv : ∀ r : R, ∀ n ∈ N, (r : G) * n * (r : G)⁻¹ ∈ N) :
    IsMulCommutative ↥N := by
  by_cases hN_bot : N = ⊥
  · subst hN_bot
    infer_instance
  · let S : Subgroup G := N ⊔ R
    let ρS : Representation F S V := ρ.comp S.subtype
    have hK_ne : K ≠ ⊥ := by
      intro hK_bot
      apply hN_bot
      refine le_antisymm ?_ bot_le
      intro y hy
      have hyK : y ∈ K := hN_lt.1 hy
      simpa [hK_bot] using hyK
    have hR_ne : R ≠ ⊥ := by
      intro hR_bot
      exact hR_prime.ne_one ((Subgroup.eq_bot_iff_card (H := R)).1 hR_bot)
    have hcentK :
        ∀ x : R, x ≠ 1 → elementCentralizerIn K (x : G) = ⊥ :=
    (lemma_3_1 (K := K) (R := R) hK_ne hR_ne hfrob.normal hfrob.isComplement').1 hfrob
    have hRnormN : R ≤ Subgroup.normalizer N := by
      intro r hr
      rw [Subgroup.mem_normalizer_iff]
      intro n
      constructor
      · intro hn
        exact hRinv ⟨r, hr⟩ n hn
      · intro hn
        have hrinv : ((⟨r, hr⟩ : R)⁻¹ : R) = ⟨(r : G)⁻¹, R.inv_mem hr⟩ := rfl
        have hconj :=
          hRinv ((⟨r, hr⟩ : R)⁻¹) ((r : G) * n * (r : G)⁻¹) hn
        simpa [hrinv, mul_assoc] using hconj
    have hNsub_normal : (N.subgroupOf S).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
      exact sup_le Subgroup.le_normalizer hRnormN
    have hNsub_ne : N.subgroupOf S ≠ ⊥ := by
      intro hNsub_bot
      apply hN_bot
      have hcard :
          Nat.card (N.subgroupOf S) = 1 :=
        (Subgroup.eq_bot_iff_card (H := N.subgroupOf S)).1 hNsub_bot
      have hcardN : Nat.card N = 1 := by
        rw [natCard_subgroupOf_eq N S le_sup_left] at hcard
        exact hcard
      exact (Subgroup.eq_bot_iff_card (H := N)).2 hcardN
    have hRsub_ne : R.subgroupOf S ≠ ⊥ := by
      intro hRsub_bot
      have hcard :
          Nat.card (R.subgroupOf S) = 1 :=
        (Subgroup.eq_bot_iff_card (H := R.subgroupOf S)).1 hRsub_bot
      have hcardR : Nat.card R = 1 := by
        rw [natCard_subgroupOf_eq R S le_sup_right] at hcard
        exact hcard
      exact hR_prime.ne_one hcardR
    have hsub_frob :
        IsFrobeniusGroupWithKernelComplement (N.subgroupOf S) (R.subgroupOf S) := by
      have hdisj : Disjoint N R := hfrob.isComplement'.disjoint.mono_left hN_lt.1
      have hsub_compl :
          (N.subgroupOf S).IsComplement' (R.subgroupOf S) :=
        by
          have htop : N.subgroupOf S ⊔ R.subgroupOf S = ⊤ := by
            calc
              N.subgroupOf S ⊔ R.subgroupOf S = (N ⊔ R).subgroupOf S := by
                symm
                simpa [S] using
                  (Subgroup.subgroupOf_sup (A := N) (A' := R) (B := S) le_sup_left le_sup_right)
              _ = ⊤ := by
                apply (Subgroup.subgroupOf_eq_top).2
                simp [S]
          refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
          · rw [Subgroup.disjoint_def]
            intro x hxN hxR
            apply Subtype.ext
            exact (Subgroup.disjoint_def.mp hdisj) hxN hxR
          · rw [Set.eq_univ_iff_forall]
            intro x
            have hxsup : x ∈ N.subgroupOf S ⊔ R.subgroupOf S := by
              rw [htop]
              trivial
            rcases (Subgroup.mem_sup_of_normal_left (x := x) (s := N.subgroupOf S)
              (t := R.subgroupOf S)).1 hxsup with ⟨n, hnN, r, hrR, hnr⟩
            refine ⟨n, hnN, r, hrR, ?_⟩
            simpa using hnr
      refine
        (lemma_3_1 (G := S) (K := N.subgroupOf S) (R := R.subgroupOf S)
          hNsub_ne hRsub_ne hNsub_normal hsub_compl).2 ?_
      intro x hx_ne
      rw [Subgroup.eq_bot_iff_forall]
      intro y hy
      rcases hy with ⟨hyN, hyC⟩
      have hxG_ne : ((x : S) : G) ≠ 1 := by
        intro hxG_eq_one
        apply hx_ne
        apply Subtype.ext
        apply Subtype.ext
        exact hxG_eq_one
      let xR : R := ⟨((x : S) : G), x.2⟩
      have hxR_ne : xR ≠ 1 := by
        intro hxR_eq_one
        exact hxG_ne (congrArg Subtype.val hxR_eq_one)
      have hyC' : (y : G) ∈ elementCentralizerIn K (xR : G) := by
        refine ⟨hN_lt.1 hyN, ?_⟩
        have hyCommS : (y : S) * (x : S) = (x : S) * (y : S) :=
          Subgroup.mem_centralizer_singleton_iff.mp hyC
        exact
          Subgroup.mem_centralizer_singleton_iff.mpr <|
            congrArg Subtype.val hyCommS
      have hybot : (y : G) ∈ (⊥ : Subgroup G) := by
        rw [hcentK xR hxR_ne] at hyC'
        simpa using hyC'
      apply Subtype.ext
      simpa using hybot
    let NK : Subgroup K := N.subgroupOf K
    let eNK : NK ≃* N := Subgroup.subgroupOfEquivOfLe (H := N) (K := K) hN_lt.1
    let : Group.IsSolvable ↥K := hsolvK
    have hsolvNK : Group.IsSolvable ↥NK := by infer_instance
    have hsolvN : Group.IsSolvable ↥N := by
      exact Group.isSolvable_of_surjective (f := eNK.toMonoidHom) eNK.surjective
    let eNS : (N.subgroupOf S) ≃* N := Subgroup.subgroupOfEquivOfLe (H := N) (K := S) le_sup_left
    have hsolvNsub : Group.IsSolvable ↥(N.subgroupOf S) := by
      let : Group.IsSolvable ↥N := hsolvN
      exact Group.isSolvable_of_surjective (f := eNS.symm.toMonoidHom) eNS.symm.surjective
    have hcard_sub_dvd : Nat.card S ∣ Nat.card G := Subgroup.card_subgroup_dvd_card S
    have hNsub_lt : Nat.card (N.subgroupOf S) < Nat.card K := by
      rw [natCard_subgroupOf_eq N S le_sup_left]
      exact natCard_lt_of_subgroup_lt hN_lt
    have hRsub_prime : Nat.Prime (Nat.card (R.subgroupOf S)) := by
      rw [natCard_subgroupOf_eq R S le_sup_right]
      exact hR_prime
    have hsub_fix :
        Module.rank F ↥(ρS.fixedSubspace (R.subgroupOf S)) = 1 := by
      dsimp [ρS]
      rw [fixedSubspace_subgroupOf_eq (ρ := ρ) (S := S) (R := R) le_sup_right]
      exact hfixR
    have hRsub_cyclic : IsCyclic ↥(R.subgroupOf S) := by
      let eRS : (R.subgroupOf S) ≃* R := Subgroup.subgroupOfEquivOfLe (H := R) (K := S) le_sup_right
      let : IsCyclic ↥R := hR_cyclic
      exact isCyclic_of_surjective (f := eRS.symm.toMonoidHom) eRS.symm.surjective
    have hsub :
        ⁅N.subgroupOf S, N.subgroupOf S⁆ ≤
          ρS.centralizerIn (N.subgroupOf S) := by
      exact
        hind (G' := S) (N.subgroupOf S) (R.subgroupOf S) ρS
          hNsub_lt
          hsub_frob
          hsolvNsub
          hRsub_cyclic
          hRsub_prime
          (hchar_of_card_dvd (G := G) (F := F) hchar hcard_sub_dvd)
          hsub_fix
    have hcomm : ⁅N, N⁆ ≤ ρ.centralizerIn N := by
      exact
        commutator_le_centralizerIn_of_subgroupOf_eq
          (ρ := ρ) (S := S) (H := N) (R := N) le_sup_left le_sup_left hsub
    have hNcent_bot : ρ.centralizerIn N = ⊥ := by
      simp [Representation.centralizerIn, hker_bot]
    have hcomm_eq_bot : ⁅N, N⁆ = ⊥ := by
      rw [hNcent_bot] at hcomm
      exact le_antisymm hcomm bot_le
    exact
      (Subgroup.le_centralizer_iff_isMulCommutative (K := N)).mp <|
        (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := N) (H₂ := N)).mp hcomm_eq_bot

theorem CFSG.theorem_3_5_commutator_abelian
    {G : Type uG} [Group G] [Finite G] {F : Type uF} [Field F] {V : Type uV}
    [AddCommGroup V] [Module F V]
    (K R : Subgroup G) (ρ : Representation F G V)
    (hind : Theorem35IndHyp.{uG, uF, uV} (F := F) K)
    (hfrob : IsFrobeniusGroupWithKernelComplement K R) (hsolvK : Group.IsSolvable K)
    (hR_cyclic : IsCyclic R) (hR_prime : Nat.Prime (Nat.card R))
    (hchar : ringChar F = 0 ∨
      (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card G)))
    (hfixR : Module.rank F ↥(ρ.fixedSubspace R) = 1)
    (hker_bot : ρ.ker = ⊥) :
    IsMulCommutative ↥⁅K, K⁆ := by
  by_cases hcomm_bot : ⁅K, K⁆ = ⊥
  · rw [hcomm_bot]
    infer_instance
  · let : Group.IsSolvable ↥K := hsolvK
    have hK_ne : K ≠ ⊥ := by
      intro hK_bot
      exact hcomm_bot (by simp [hK_bot])
    let : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).2 hK_ne
    have hcomm_lt_top : commutator (↥K) < (⊤ : Subgroup ↥K) :=
      Group.IsSolvable.commutator_lt_top_of_nontrivial (G := ↥K)
    have hcomm_lt : ⁅K, K⁆ < K := by
      have hlt' :
          (commutator (↥K)).map K.subtype < (⊤ : Subgroup ↥K).map K.subtype :=
        (Subgroup.map_subtype_lt_map_subtype (G' := K)
          (H := commutator (↥K)) (K := (⊤ : Subgroup ↥K))).mpr hcomm_lt_top
      have htop_map : (⊤ : Subgroup ↥K).map K.subtype = K := by
        simpa [MonoidHom.range_eq_map] using (K.range_subtype : K.subtype.range = K)
      simpa [Subgroup.map_subtype_commutator, htop_map] using hlt'
    let : K.Normal := hfrob.normal
    let : (⁅K, K⁆).Normal := inferInstance
    have hRinv_comm :
        ∀ r : R, ∀ x ∈ ⁅K, K⁆, (r : G) * x * (r : G)⁻¹ ∈ ⁅K, K⁆ := by
      intro r x hx
      exact (inferInstance : (⁅K, K⁆).Normal).conj_mem x hx r
    exact
      theorem_3_5_proper_invariant_subgroups_abelian K R ρ hind hfrob hsolvK hR_cyclic
        hR_prime hchar hfixR hker_bot ⁅K, K⁆ hcomm_lt hRinv_comm

theorem CFSG.theorem_3_5_le_ker_of_equiv
    {G : Type*} [Group G] {F : Type*} [Field F] {V W : Type*}
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    {ρ : Representation F G V} {σ : Representation F G W}
    (e : ρ ≃ₗ σ) {H : Subgroup G} (hH : H ≤ σ.ker) :
    H ≤ ρ.ker := by
  intro h hh
  rw [MonoidHom.mem_ker]
  ext v
  apply e.injective
  have hσ : σ h (e v) = e v := by
    have hh' : h ∈ σ.ker := hH hh
    exact DFunLike.congr_fun (show σ h = 1 by simpa using hh') (e v)
  simpa using (e.isIntertwining h v).trans hσ

noncomputable def CFSG.theorem_3_5_fixedSubspace_equiv_of_equiv
    {G : Type*} [Group G] {F : Type*} [Field F] {V W : Type*}
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    {ρ : Representation F G V} {σ : Representation F G W}
    (e : ρ ≃ₗ σ) (R : Subgroup G) :
    ρ.fixedSubspace R ≃ₗ[F] σ.fixedSubspace R := by
  refine
    { toFun := fun v => ⟨e v, ?_⟩
      invFun := fun w => ⟨e.symm w, ?_⟩
      left_inv := ?_
      right_inv := ?_
      map_add' := by
        intro v w
        ext1
        exact e.map_add v w
      map_smul' := by
        intro a v
        ext1
        exact e.map_smul a v }
  · change ∀ r : R, σ r (e v) = e v
    intro r
    simpa using (e.isIntertwining r v).symm.trans (congrArg e (v.2 r))
  · change ∀ r : R, ρ r (e.symm w) = e.symm w
    intro r
    simpa using (e.symm.isIntertwining r w).symm.trans (congrArg e.symm (w.2 r))
  · intro v
    ext1
    simp
  · intro w
    ext1
    simp

noncomputable def CFSG.theorem_3_5_projectionRepMapOfIsCompl
    {G : Type*} [Group G] {F : Type*} [Field F] {V : Type*}
    [AddCommGroup V] [Module F V] {ρ : Representation F G V}
    (P Q : Subrepresentation ρ) (hPQ : IsCompl P.toSubmodule Q.toSubmodule) :
    ρ →ₗ P.toRepresentation := by
  let proj : V →ₗ[F] P.toSubmodule :=
    Submodule.projectionOnto P.toSubmodule Q.toSubmodule hPQ
  have hproj_intertwining (g : G) :
      proj.comp (ρ g) = (P.toRepresentation g).comp proj := by
    apply LinearMap.ext
    intro v
    rcases Submodule.existsUnique_add_of_isCompl hPQ v with ⟨u, w, huw, huniq⟩
    have hu_mem : ρ g u ∈ P.toSubmodule := P.apply_mem_toSubmodule g u.2
    have hw_mem : ρ g w ∈ Q.toSubmodule := Q.apply_mem_toSubmodule g w.2
    let projQ : V →ₗ[F] Q.toSubmodule :=
      Submodule.projectionOnto Q.toSubmodule P.toSubmodule hPQ.symm
    have hdecomp : (proj v : V) + (projQ v : V) = v := by
      simpa [proj, projQ] using
        Submodule.projection_add_projection_eq_self hPQ v
    have hproj_v : proj v = u := by
      exact huniq (proj v) (projQ v) hdecomp |>.1
    have hproj_hu : proj ((ρ g) u) = ⟨(ρ g) u, hu_mem⟩ := by
      simpa [proj] using
        Submodule.projectionOnto_apply_left hPQ ⟨(ρ g) u, hu_mem⟩
    have hproj_hw : proj ((ρ g) w) = 0 := by
      simpa [proj] using
        Submodule.projectionOnto_apply_right hPQ ⟨(ρ g) w, hw_mem⟩
    apply Subtype.ext
    calc
      (((proj.comp (ρ g)) v : P.toSubmodule) : V) =
          ((proj ((ρ g) u + (ρ g) w) : P.toSubmodule) : V) := by
            rw [LinearMap.comp_apply, ← huw, map_add]
      _ = ((proj ((ρ g) u) : P.toSubmodule) : V) +
          ((proj ((ρ g) w) : P.toSubmodule) : V) := by
            simp [map_add]
      _ = (ρ g) u + 0 := by
            rw [hproj_hu, hproj_hw]
            simp
      _ = (ρ g) u := by simp
      _ = (ρ g) (proj v) := by rw [congrArg Subtype.val hproj_v.symm]
      _ = (((P.toRepresentation g).comp proj v : P.toSubmodule) : V) := by
            rfl
  exact Theory.Representation.RepMap.mk proj hproj_intertwining

noncomputable def CFSG.theorem_3_5_fixedSubspace_prodEquivOfIsCompl
    {G : Type*} [Group G] {F : Type*} [Field F] {V : Type*}
    [AddCommGroup V] [Module F V] {ρ : Representation F G V}
    (P Q : Subrepresentation ρ) (hPQ : IsCompl P.toSubmodule Q.toSubmodule) (H : Subgroup G) :
    ρ.fixedSubspace H ≃ₗ[F]
      (P.toRepresentation.fixedSubspace H × Q.toRepresentation.fixedSubspace H) := by
  let projP : ρ →ₗ P.toRepresentation := theorem_3_5_projectionRepMapOfIsCompl P Q hPQ
  let projQ : ρ →ₗ Q.toRepresentation := theorem_3_5_projectionRepMapOfIsCompl Q P hPQ.symm
  let projP' : V →ₗ[F] P.toSubmodule :=
    Submodule.projectionOnto P.toSubmodule Q.toSubmodule hPQ
  let projQ' : V →ₗ[F] Q.toSubmodule :=
    Submodule.projectionOnto Q.toSubmodule P.toSubmodule hPQ.symm
  have hdecomp (v : V) :
      ((projP v : P.toSubmodule) : V) + ((projQ v : Q.toSubmodule) : V) = v := by
    change (projP' v : V) + (projQ' v : V) = v
    simpa [projP', projQ'] using
      Submodule.projection_add_projection_eq_self hPQ v
  have hprojP_left (u : P.toSubmodule) : projP u = u := by
    change projP' u = u
    exact Submodule.projectionOnto_apply_left hPQ u
  have hprojP_right (u : Q.toSubmodule) : projP u = 0 := by
    change projP' u = 0
    exact Submodule.projectionOnto_apply_right hPQ u
  have hprojQ_left (u : Q.toSubmodule) : projQ u = u := by
    change projQ' u = u
    exact Submodule.projectionOnto_apply_left hPQ.symm u
  have hprojQ_right (u : P.toSubmodule) : projQ u = 0 := by
    change projQ' u = 0
    exact Submodule.projectionOnto_apply_right hPQ.symm u
  let e :
      ρ.fixedSubspace H ≃ₗ[F]
        (P.toRepresentation.fixedSubspace H × Q.toRepresentation.fixedSubspace H) := by
    refine
        { toFun := fun v => (⟨projP v, ?_⟩, ⟨projQ v, ?_⟩)
          invFun := fun vw => ⟨vw.1.1 + vw.2.1, ?_⟩
          left_inv := ?_
          right_inv := ?_
          map_add' := by
            intro v w
            ext <;> simp
          map_smul' := by
            intro a v
            ext <;> simp }
    · change ∀ h : H, P.toRepresentation h (projP v) = projP v
      intro h
      have hv :=
        (Representation.IntertwiningMap.isIntertwining
          (ρ := ρ) (σ := P.toRepresentation) projP h v).symm.trans (congrArg projP (v.2 h))
      change P.toRepresentation h (projP v) = projP v at hv
      exact hv
    · change ∀ h : H, Q.toRepresentation h (projQ v) = projQ v
      intro h
      have hv :=
        (Representation.IntertwiningMap.isIntertwining
          (ρ := ρ) (σ := Q.toRepresentation) projQ h v).symm.trans (congrArg projQ (v.2 h))
      change Q.toRepresentation h (projQ v) = projQ v at hv
      exact hv
    · change ∀ h : H, ρ h (vw.1.1 + vw.2.1) = vw.1.1 + vw.2.1
      intro h
      have hvP : ρ h vw.1.1 = vw.1.1 := by
        exact congrArg Subtype.val (vw.1.2 h)
      have hvQ : ρ h vw.2.1 = vw.2.1 := by
        exact congrArg Subtype.val (vw.2.2 h)
      simp [hvP, hvQ]
    · intro v
      apply Subtype.ext
      exact hdecomp v
    · intro vw
      refine Prod.ext ?_ ?_
      · apply Subtype.ext
        change projP.toLinearMap (vw.1.1 + vw.2.1) = vw.1.1
        have hleft : projP.toLinearMap (↑↑vw.1 : V) = vw.1.1 := by
          have hleft' := hprojP_left vw.1.1
          change projP.toLinearMap (↑↑vw.1 : V) = vw.1.1 at hleft'
          exact hleft'
        have hright : projP.toLinearMap (↑↑vw.2 : V) = 0 := by
          have hright' := hprojP_right vw.2.1
          change projP.toLinearMap (↑↑vw.2 : V) = 0 at hright'
          exact hright'
        rw [map_add, hleft, hright, add_zero]
      · apply Subtype.ext
        change projQ.toLinearMap (vw.1.1 + vw.2.1) = vw.2.1
        have hleft : projQ.toLinearMap (↑↑vw.1 : V) = 0 := by
          have hleft' := hprojQ_right vw.1.1
          change projQ.toLinearMap (↑↑vw.1 : V) = 0 at hleft'
          exact hleft'
        have hright : projQ.toLinearMap (↑↑vw.2 : V) = vw.2.1 := by
          have hright' := hprojQ_left vw.2.1
          change projQ.toLinearMap (↑↑vw.2 : V) = vw.2.1 at hright'
          exact hright'
        rw [map_add, hleft, hright, zero_add]
  exact e

noncomputable def CFSG.theorem_3_5_fixedSubrepresentation_of_normal
    {G : Type*} [Group G] {F : Type*} [Field F] {V : Type*}
    [AddCommGroup V] [Module F V] (ρ : Representation F G V)
    (H : Subgroup G) [H.Normal] :
    Subrepresentation ρ where
  toSubmodule := ρ.fixedSubspace H
  apply_mem_toSubmodule := by
    intro g v hv
    change ∀ h : H, ρ h (ρ g v) = ρ g v
    intro h
    have hh' : (g : G)⁻¹ * h * g ∈ H := by
      simpa using Subgroup.Normal.conj_mem (inferInstance : H.Normal) h h.2 ((g : G)⁻¹)
    let h' : H := ⟨(g : G)⁻¹ * h * g, hh'⟩
    have hvh' : ρ h' v = v := hv h'
    calc
      ρ h (ρ g v) = ((ρ h) * (ρ g)) v := rfl
      _ = ρ ((h : G) * g) v := by rw [← ρ.map_mul]
      _ = ρ (g * (h' : H)) v := by
            congr 1
            simp [h', mul_assoc]
      _ = ((ρ g) * (ρ h')) v := by rw [ρ.map_mul]
      _ = ρ g (ρ h' v) := rfl
      _ = ρ g v := by rw [hvh']

theorem CFSG.theorem_3_5_le_ker_of_normal_fixedSubspace_ne_bot
    {G : Type*} [Group G] {F : Type*} [Field F] {V : Type*}
    [AddCommGroup V] [Module F V] (ρ : Representation F G V)
    (H : Subgroup G) [H.Normal] [Representation.IsIrreducible ρ]
    (hfix : ρ.fixedSubspace H ≠ ⊥) :
    H ≤ ρ.ker := by
  let S : Subrepresentation ρ := theorem_3_5_fixedSubrepresentation_of_normal ρ H
  have hS_ne : S ≠ ⊥ := by
    intro hS
    apply hfix
    have hS' := congrArg Subrepresentation.toSubmodule hS
    change ρ.fixedSubspace H = (⊥ : Submodule F V) at hS'
    exact hS'
  have hS_top : S = ⊤ := by
    rcases (inferInstance : Representation.IsIrreducible ρ).eq_bot_or_eq_top S with hbot | htop
    · exact False.elim (hS_ne hbot)
    · exact htop
  have htop_sub : ρ.fixedSubspace H = ⊤ := by
    have hS_top' := congrArg Subrepresentation.toSubmodule hS_top
    change ρ.fixedSubspace H = (⊤ : Submodule F V) at hS_top'
    exact hS_top'
  intro h hh
  rw [MonoidHom.mem_ker]
  ext v
  have hv : v ∈ ρ.fixedSubspace H := by simp [htop_sub]
  exact hv ⟨h, hh⟩


noncomputable def CFSG.theorem_3_5_coindMap
    {F : Type*} [Field F] {G : Type*} [Group G] {H : Subgroup G} [H.Normal]
    {V : Type*} [AddCommGroup V] [Module F V] {W : Type*}
    [AddCommGroup W] [Module F W] (σ : Representation F G W)
    (ρ : Representation F H V) (π : σ.comp H.subtype →ₗ ρ) :
    σ →ₗ coindRep ρ := by
  refine Theory.Representation.RepMap.mk ?_ ?_
  · refine
      { toFun := fun w => ⟨fun g => π (σ g w), ?_⟩
        map_add' := by
          intro w1 w2
          apply Subtype.ext
          ext g
          simp
        map_smul' := by
          intro a w
          apply Subtype.ext
          ext g
          simp }
    intro h g
    have hπ := Representation.IntertwiningMap.isIntertwining
      (ρ := σ.comp H.subtype) (σ := ρ) π h (σ g w)
    change π (σ (h : G) (σ g w)) = ρ h (π (σ g w)) at hπ
    change π (σ ((h : G) * g) w) = ρ h (π (σ g w))
    simpa using hπ
  · intro g
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    ext x
    change π (σ x (σ g w)) = π (σ (x * g) w)
    rw [σ.map_mul]
    rfl

private theorem CFSG.theorem_3_5_coindEval_coindMap
    {F : Type*} [Field F] {G : Type*} [Group G] {H : Subgroup G} [H.Normal]
    {V : Type*} [AddCommGroup V] [Module F V] {W : Type*}
    [AddCommGroup W] [Module F W] (σ : Representation F G W)
    (ρ : Representation F H V) (π : σ.comp H.subtype →ₗ ρ) (g : G) (w : W) :
    coindEval (ρ := ρ) g (theorem_3_5_coindMap σ ρ π w) = π (σ g w) := rfl

noncomputable def CFSG.theorem_3_5_coindMapOfSubrep
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G] {H : Subgroup G} [H.Normal]
    {V : Type*} [AddCommGroup V] [Module F V] (σ : Representation F G V)
    (hchar : ringChar F = 0 ∨
      (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card H)))
    (M : Subrepresentation (σ.comp H.subtype)) :
    σ →ₗ coindRep M.toRepresentation := by
  let σH : Representation F H V := σ.comp H.subtype
  have hσHcr : σH.IsCompletelyReducible := by
    exact Representation.isCompletelyReducible_of_ringChar_eq_zero_or_prime_coprime (ρ := σH) hchar
  let : ComplementedLattice (Subrepresentation σH) := by
    exact
      (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule
        (ρ := σH)).2 hσHcr
  let ψ : Subrepresentation σH := Classical.choose (exists_isCompl M)
  have hcompl : IsCompl M ψ := Classical.choose_spec (exists_isCompl M)
  have hcompl_sub : IsCompl M.toSubmodule ψ.toSubmodule := by
    refine ⟨?_, ?_⟩
    · rw [disjoint_iff]
      have h := congrArg Subrepresentation.toSubmodule hcompl.inf_eq_bot
      change M.toSubmodule ⊓ ψ.toSubmodule = (⊥ : Submodule F V) at h
      exact h
    · rw [codisjoint_iff]
      have h := congrArg Subrepresentation.toSubmodule hcompl.sup_eq_top
      change M.toSubmodule ⊔ ψ.toSubmodule = (⊤ : Submodule F V) at h
      exact h
  let proj : V →ₗ[F] M.toSubmodule :=
    Submodule.projectionOnto M.toSubmodule ψ.toSubmodule hcompl_sub
  have hproj_intertwining (h : H) :
      proj.comp (σH h) = (M.toRepresentation h).comp proj := by
    apply LinearMap.ext
    intro v
    rcases Submodule.existsUnique_add_of_isCompl hcompl_sub v with ⟨u, w, huw, huniq⟩
    have hu_mem : (σH h) u ∈ M.toSubmodule := M.apply_mem_toSubmodule h u.2
    have hw_mem : (σH h) w ∈ ψ.toSubmodule := ψ.apply_mem_toSubmodule h w.2
    let projψ : V →ₗ[F] ψ.toSubmodule :=
      Submodule.projectionOnto ψ.toSubmodule M.toSubmodule hcompl_sub.symm
    have hdecomp : (proj v : V) + (projψ v : V) = v := by
      simpa [proj, projψ] using Submodule.projection_add_projection_eq_self hcompl_sub v
    have hproj_v : proj v = u := by
      exact huniq (proj v) (projψ v) hdecomp |>.1
    have hproj_hu : proj ((σH h) u) = ⟨(σH h) u, hu_mem⟩ := by
      simpa [proj] using Submodule.projectionOnto_apply_left hcompl_sub ⟨(σH h) u, hu_mem⟩
    have hproj_hw : proj ((σH h) w) = 0 := by
      simpa [proj] using Submodule.projectionOnto_apply_right hcompl_sub ⟨(σH h) w, hw_mem⟩
    apply Subtype.ext
    calc
      (((proj.comp (σH h)) v : M.toSubmodule) : V) =
          ((proj ((σH h) u + (σH h) w) : M.toSubmodule) : V) := by
            rw [LinearMap.comp_apply, ← huw, map_add]
      _ = ((proj ((σH h) u) : M.toSubmodule) : V) + ((proj ((σH h) w) : M.toSubmodule) : V) := by
            simp [map_add]
      _ = (σH h) u + 0 := by
            rw [hproj_hu, hproj_hw]
            simp
      _ = (σH h) u := by simp
      _ = (σH h) (proj v) := by rw [congrArg Subtype.val hproj_v.symm]
      _ = (((M.toRepresentation h).comp proj v : M.toSubmodule) : V) := by rfl
  exact
    theorem_3_5_coindMap σ M.toRepresentation
      (Theory.Representation.RepMap.mk proj hproj_intertwining)

theorem CFSG.theorem_3_5_coindMapOfSubrep_eval_one
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G] {H : Subgroup G} [H.Normal]
    {V : Type*} [AddCommGroup V] [Module F V] (σ : Representation F G V)
    (hchar : ringChar F = 0 ∨
      (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card H)))
    (M : Subrepresentation (σ.comp H.subtype)) (m : M.toSubmodule) :
    coindEval (ρ := M.toRepresentation) (1 : G)
      (theorem_3_5_coindMapOfSubrep σ hchar M m) = m := by
  classical
  unfold theorem_3_5_coindMapOfSubrep
  simp only [theorem_3_5_coindEval_coindMap, map_one, Module.End.one_apply,
    Theory.Representation.RepMap.coe_mk, Submodule.projectionOnto_apply_left]

theorem CFSG.theorem_3_5_coind_apply_baseFunctionAt
    {F : Type*} [Field F] {G : Type*} [Group G] {H : Subgroup G} [H.Normal]
    {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F H V)
    (g x : G) (v : V) :
    coindRep (ρ := ρ) x (coindBaseFunctionAt (ρ := ρ) g v) =
      coindBaseFunctionAt (ρ := ρ) (g * x⁻¹) v := by
  classical
  ext y
  change (coindBaseFunctionAt (ρ := ρ) g v).1 (y * x) =
    (coindBaseFunctionAt (ρ := ρ) (g * x⁻¹) v).1 y
  unfold coindBaseFunctionAt
  change (if hx : y * x * g⁻¹ ∈ H then ρ ⟨y * x * g⁻¹, hx⟩ v else 0) =
    (if hx : y * (g * x⁻¹)⁻¹ ∈ H then ρ ⟨y * (g * x⁻¹)⁻¹, hx⟩ v else 0)
  by_cases h1 : y * x * g⁻¹ ∈ H
  · by_cases h2 : y * (g * x⁻¹)⁻¹ ∈ H
    · simp [mul_assoc, mul_inv_rev]
    · exfalso
      exact h2 (by simpa [mul_assoc, mul_inv_rev] using h1)
  · by_cases h2 : y * (g * x⁻¹)⁻¹ ∈ H
    · exfalso
      exact h1 (by simpa [mul_assoc, mul_inv_rev] using h2)
    · simp [mul_assoc, mul_inv_rev]

theorem CFSG.theorem_3_5_coind_sumBase_mem_fixedSubspace
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G] {H R : Subgroup G}
    [H.Normal] [Fintype R] {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F H V) (v : V) :
    (∑ r : R, coindBaseFunctionAt (ρ := ρ) (r : G) v) ∈
      (coindRep (ρ := ρ)).fixedSubspace R := by
  classical
  change ∀ r : R,
      coindRep (ρ := ρ) r (∑ s : R, coindBaseFunctionAt (ρ := ρ) (s : G) v) =
        ∑ s : R, coindBaseFunctionAt (ρ := ρ) (s : G) v
  intro r
  rw [map_sum]
  calc
    ∑ s : R, coindRep (ρ := ρ) r (coindBaseFunctionAt (ρ := ρ) (s : G) v) =
        ∑ s : R, coindBaseFunctionAt (ρ := ρ) ((s : G) * (r : G)⁻¹) v := by
          apply Fintype.sum_congr
          intro s
          simpa using
            theorem_3_5_coind_apply_baseFunctionAt (ρ := ρ) (g := (s : G)) (x := (r : G)) v
    _ = ∑ s : R, coindBaseFunctionAt (ρ := ρ) (s : G) v := by
          let e : R → R := fun s => s * r⁻¹
          have he : Function.Bijective e := Group.mulRight_bijective r⁻¹
          simpa [e] using
            (Fintype.sum_bijective e he
              (fun s : R => coindBaseFunctionAt (ρ := ρ) ((s : G) * (r : G)⁻¹) v)
              (fun s : R => coindBaseFunctionAt (ρ := ρ) (s : G) v)
              (fun s => rfl))

theorem CFSG.theorem_3_5_coindEval_surjective_fixedSubspace
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G] {H R : Subgroup G}
    [H.Normal] {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F H V) (hHR : H.IsComplement' R) :
    Function.Surjective
      ((coindEval (ρ := ρ) (1 : G)).toLinearMap.comp
        ((coindRep (ρ := ρ)).fixedSubspace R).subtype) := by
  classical
  let : Fintype R := Fintype.ofFinite R
  intro v
  refine ⟨⟨∑ r : R, coindBaseFunctionAt (ρ := ρ) (r : G) v, ?_⟩, ?_⟩
  · exact theorem_3_5_coind_sumBase_mem_fixedSubspace (ρ := ρ) v
  · change (coindEval (ρ := ρ) (1 : G)).toLinearMap
      (∑ r : R, coindBaseFunctionAt (ρ := ρ) (r : G) v) = v
    rw [map_sum]
    rw [Finset.sum_eq_single (1 : R)]
    · exact coindEval_base (ρ := ρ) (1 : G) v
    · intro r _ hr
      have hrq :
          ((r : G) : G ⧸ H) ≠ 1 := by
        intro hq
        have hrH : (r : G) ∈ H := (QuotientGroup.eq_one_iff _).mp hq
        have hr1 : (r : G) = 1 := by
          exact (Subgroup.disjoint_def.mp hHR.disjoint) hrH r.2
        exact hr (Subtype.ext hr1)
      have hrq' : ((1 : G) : G ⧸ H) ≠ ((r : G) : G ⧸ H) := by
        intro hq
        apply hrq
        simpa using hq.symm
      have hzero :=
        coindEval_of_ne_coset (ρ := ρ) (x := (1 : G)) (g := (r : G)) hrq' v
      change coindEval (ρ := ρ) (1 : G)
        (coindBaseFunctionAt (ρ := ρ) (r : G) v) = 0 at hzero
      exact hzero
    · intro hr
      exact False.elim (hr (Finset.mem_univ _))

theorem CFSG.theorem_3_5_le_ker_coind_of_le_ker
    {F : Type*} [Field F] {G : Type*} [Group G] {H N : Subgroup G}
    [H.Normal] [N.Normal] {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F H V) (hN_le_H : N ≤ H) (hNker : N.subgroupOf H ≤ ρ.ker) :
    N ≤ (coindRep (ρ := ρ)).ker := by
  intro n hn
  rw [MonoidHom.mem_ker]
  ext f x
  have hconjN : x * n * x⁻¹ ∈ N := by
    simpa using (inferInstance : N.Normal).conj_mem n hn x
  have hconjH : x * n * x⁻¹ ∈ H := hN_le_H hconjN
  have hker : ρ ⟨x * n * x⁻¹, hconjH⟩ = 1 := by
    have hmem : (⟨x * n * x⁻¹, hconjH⟩ : H) ∈ N.subgroupOf H := by
      exact hconjN
    exact MonoidHom.mem_ker.mp (hNker hmem)
  have hf : f.1 (x * n) = ρ ⟨x * n * x⁻¹, hconjH⟩ (f.1 x) := by
    simpa [mul_assoc] using (f.2 ⟨x * n * x⁻¹, hconjH⟩ x)
  calc
    f.1 (x * n) = ρ ⟨x * n * x⁻¹, hconjH⟩ (f.1 x) := hf
    _ = f.1 x := by simpa using DFunLike.congr_fun hker (f.1 x)

theorem CFSG.theorem_3_5_invariants_extendScalars_eq_baseChange
    {G : Type*} [Group G] [Finite G] {F : Type*} [Field F]
    {F' : Type*} [Field F'] [Algebra F F'] {V : Type*}
    [AddCommGroup V] [Module F V] (ρ : Representation F G V)
    (hF : (Nat.card G : F) ≠ 0) (hF' : (Nat.card G : F') ≠ 0) :
    Representation.invariants (Theory.Representation.extendScalars F' ρ) =
      (Representation.invariants ρ).baseChange F' := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Invertible (Fintype.card G : F) := by
    simpa [Nat.card_eq_fintype_card] using invertibleOfNonzero hF
  let : Invertible (Fintype.card G : F') := by
    simpa [Nat.card_eq_fintype_card] using invertibleOfNonzero hF'
  let S : Submodule F V := Representation.invariants ρ
  let S' : Submodule F' (F' ⊗[F] V) :=
    Representation.invariants (Theory.Representation.extendScalars F' ρ)
  let avg : V →ₗ[F] V := Representation.averageMap ρ
  let avgS : V →ₗ[F] ↥S :=
    avg.codRestrict S (Representation.averageMap_invariant (ρ := ρ))
  let avg' : F' ⊗[F] V →ₗ[F'] F' ⊗[F] V :=
    Representation.averageMap (Theory.Representation.extendScalars F' ρ)
  let avgS' : F' ⊗[F] V →ₗ[F'] ↥S' :=
    avg'.codRestrict S'
      (Representation.averageMap_invariant (ρ := Theory.Representation.extendScalars F' ρ))
  have havg_eq : avg' = LinearMap.baseChange F' avg := by
    ext a
    simp [avg', avg, Representation.averageMap, GroupAlgebra.average,
      Theory.Representation.extendScalars_apply, map_sum, TensorProduct.AlgebraTensorModule.curry_apply]
    rw [Finset.smul_sum]
    simp_rw [TensorProduct.smul_tmul']
    rw [TensorProduct.tmul_sum]
    simp [Algebra.smul_def]
  have havgS_subtype : S.subtype.comp avgS = avg := by
    ext v
    rfl
  have havgS_proj_apply (v : S) : avgS (S.subtype v) = v := by
    apply Subtype.ext
    change avg (S.subtype v) = S.subtype v
    exact Representation.averageMap_id (ρ := ρ) v v.2
  have havgS'_subtype : S'.subtype.comp avgS' = avg' := by
    ext v
    rfl
  have havgS'_proj_apply (v : S') : avgS' (S'.subtype v) = v := by
    apply Subtype.ext
    change avg' (S'.subtype v) = S'.subtype v
    exact Representation.averageMap_id (ρ := Theory.Representation.extendScalars F' ρ) v v.2
  have hrange_avg : LinearMap.range avg = S := by
    rw [← havgS_subtype, LinearMap.range_comp]
    rw [LinearMap.range_eq_of_proj havgS_proj_apply, Submodule.map_top, Submodule.range_subtype]
  have hrange_avg' : LinearMap.range avg' = S' := by
    rw [← havgS'_subtype, LinearMap.range_comp]
    rw [LinearMap.range_eq_of_proj havgS'_proj_apply, Submodule.map_top,
      Submodule.range_subtype]
  have hbc_comp :
      (LinearMap.baseChange F' S.subtype).comp (LinearMap.baseChange F' avgS) =
        LinearMap.baseChange F' avg := by
    rw [← LinearMap.baseChange_comp, havgS_subtype]
  have hbc_proj_eq :
      (LinearMap.baseChange F' avgS).comp (LinearMap.baseChange F' S.subtype) =
        LinearMap.id := by
    ext c
    exact congrArg (fun x => (1 : F') ⊗ₜ[F] x) (havgS_proj_apply c)
  have hbc_surj : Function.Surjective (LinearMap.baseChange F' avgS) := by
    intro a
    refine ⟨(LinearMap.baseChange F' S.subtype) a, ?_⟩
    simpa using DFunLike.congr_fun hbc_proj_eq a
  have hrange_avg_bc :
      LinearMap.range (LinearMap.baseChange F' avg) = S.baseChange F' := by
    rw [← hbc_comp, LinearMap.range_comp]
    rw [LinearMap.range_eq_top.2 hbc_surj, Submodule.map_top, Submodule.baseChange]
  calc
    S' = LinearMap.range avg' := hrange_avg'.symm
    _ = LinearMap.range (LinearMap.baseChange F' avg) := by rw [havg_eq]
    _ = S.baseChange F' := hrange_avg_bc

theorem CFSG.theorem_3_5_fixedSubspace_extendScalars_eq_baseChange
    {G : Type*} [Group G] [Finite G] {F : Type*} [Field F]
    {F' : Type*} [Field F'] [Algebra F F'] {V : Type*}
    [AddCommGroup V] [Module F V] (ρ : Representation F G V) (H : Subgroup G)
    (hF : (Nat.card H : F) ≠ 0) (hF' : (Nat.card H : F') ≠ 0) :
    (Theory.Representation.extendScalars F' ρ).fixedSubspace H =
      (ρ.fixedSubspace H).baseChange F' := by
  dsimp [Representation.fixedSubspace]
  have hrep :
      (Theory.Representation.extendScalars F' ρ).comp H.subtype =
        Theory.Representation.extendScalars F' (ρ.comp H.subtype) := by
    ext h
    rfl
  rw [hrep]
  exact theorem_3_5_invariants_extendScalars_eq_baseChange
    (ρ := ρ.comp H.subtype) hF hF'

theorem CFSG.theorem_3_5_fixedSubspace_rank_one_extendScalars
    {G : Type*} [Group G] [Finite G] {F : Type*} [Field F]
    {F' : Type*} [Field F'] [Algebra F F'] {V : Type*}
    [AddCommGroup V] [Module F V] (ρ : Representation F G V) (H : Subgroup G)
    (hF : (Nat.card H : F) ≠ 0) (hF' : (Nat.card H : F') ≠ 0)
    (hfix : Module.rank F ↥(ρ.fixedSubspace H) = 1) :
    Module.rank F' ↥((Theory.Representation.extendScalars F' ρ).fixedSubspace H) = 1 := by
  have hfix_bc :
      (Theory.Representation.extendScalars F' ρ).fixedSubspace H =
        (ρ.fixedSubspace H).baseChange F' :=
    theorem_3_5_fixedSubspace_extendScalars_eq_baseChange
      (ρ := ρ) (H := H) hF hF'
  rw [hfix_bc]
  let f : F' ⊗[F] ↥(ρ.fixedSubspace H) →ₗ[F'] F' ⊗[F] V :=
    LinearMap.baseChange F' (ρ.fixedSubspace H).subtype
  have hf_inj : Function.Injective f := by
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := F') _ Subtype.val_injective
  calc
    Module.rank F' ↥((ρ.fixedSubspace H).baseChange F') = Module.rank F' (LinearMap.range f) := by
      rfl
    _ = Module.rank F' (F' ⊗[F] ↥(ρ.fixedSubspace H)) := rank_range_of_injective f hf_inj
    _ = Cardinal.lift (Module.rank F ↥(ρ.fixedSubspace H)) := by
      simp
    _ = 1 := by simp [hfix]

theorem CFSG.theorem_3_5_commutator_le_ker_of_finrank_one
    {G : Type*} [Group G] {F : Type*} [Field F] {V : Type*}
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) (hfin : Module.finrank F V = 1) :
    commutator G ≤ ρ.ker := by
  have hscalar (g : G) : ∃ a : F, ∀ v : V, ρ g v = a • v := by
    obtain ⟨a, ha, -⟩ :=
      LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one
        (R := F) (M := V) hfin (ρ g)
    refine ⟨a, ?_⟩
    intro v
    simpa using congrArg (fun f : Module.End F V => f v) ha
  have hmul_comm (g1 g2 : G) : ρ g1 * ρ g2 = ρ g2 * ρ g1 := by
    refine LinearMap.ext fun v : V => ?_
    obtain ⟨a1, ha1⟩ := hscalar g1
    obtain ⟨a2, ha2⟩ := hscalar g2
    calc
      (ρ g1 * ρ g2) v = ρ g1 (ρ g2 v) := rfl
      _ = ρ g1 (a2 • v) := by rw [ha2]
      _ = a2 • ρ g1 v := by rw [map_smul]
      _ = a2 • (a1 • v) := by rw [ha1]
      _ = (a2 * a1) • v := by rw [smul_smul]
      _ = (a1 * a2) • v := by rw [mul_comm]
      _ = a1 • (a2 • v) := by rw [smul_smul]
      _ = a1 • ρ g2 v := by rw [ha2]
      _ = ρ g2 (a1 • v) := by rw [map_smul]
      _ = ρ g2 (ρ g1 v) := by rw [ha1]
      _ = (ρ g2 * ρ g1) v := rfl
  rw [commutator_eq_closure, Subgroup.closure_le]
  rintro c ⟨g1, g2, rfl⟩
  change ρ (g1 * g2 * g1⁻¹ * g2⁻¹) = 1
  have hcomm' : ρ g2 * ρ g1⁻¹ = ρ g1⁻¹ * ρ g2 := by
    calc
      ρ g2 * ρ g1⁻¹ = ρ (g2 * g1⁻¹) := (map_mul ρ g2 g1⁻¹).symm
      _ = ρ (g1⁻¹ * g2) := by
        have := hmul_comm g2 g1⁻¹
        simpa [map_mul] using this
      _ = ρ g1⁻¹ * ρ g2 := map_mul ρ g1⁻¹ g2
  have hg1 : ρ g1 * ρ g1⁻¹ = 1 := by
    calc
      ρ g1 * ρ g1⁻¹ = ρ (g1 * g1⁻¹) := (map_mul ρ g1 g1⁻¹).symm
      _ = 1 := by simp
  have hg2 : ρ g2 * ρ g2⁻¹ = 1 := by
    calc
      ρ g2 * ρ g2⁻¹ = ρ (g2 * g2⁻¹) := (map_mul ρ g2 g2⁻¹).symm
      _ = 1 := by simp
  calc
    ρ (g1 * g2 * g1⁻¹ * g2⁻¹) = ρ g1 * (ρ g2 * ρ g1⁻¹) * ρ g2⁻¹ := by
      simp [map_mul, mul_assoc]
    _ = ρ g1 * (ρ g1⁻¹ * ρ g2) * ρ g2⁻¹ := by rw [hcomm']
    _ = (ρ g1 * ρ g1⁻¹) * (ρ g2 * ρ g2⁻¹) := by
      simp [mul_assoc]
    _ = 1 := by simp [hg1, hg2]

theorem CFSG.theorem_3_5_le_ker_of_extendScalars
    {G : Type*} [Group G] {F : Type*} [Field F] {F' : Type*} [Field F']
    [Algebra F F'] {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) {H : Subgroup G}
    (hH : H ≤ (Theory.Representation.extendScalars F' ρ).ker) :
    H ≤ ρ.ker := by
  intro h hh
  rw [MonoidHom.mem_ker]
  ext v
  have hh' : h ∈ (Theory.Representation.extendScalars F' ρ).ker := hH hh
  have hfix :
      Theory.Representation.extendScalars F' ρ h (1 ⊗ₜ[F] v) = (1 : F') ⊗ₜ[F] v := by
    simpa using
      DFunLike.congr_fun (show Theory.Representation.extendScalars F' ρ h = 1 by simpa using hh')
        ((1 : F') ⊗ₜ[F] v)
  have hfix' : (1 : F') ⊗ₜ[F] (ρ h v) = (1 : F') ⊗ₜ[F] v := by
    simpa [Theory.Representation.extendScalars_apply] using hfix
  exact (Module.FaithfullyFlat.tensorProduct_mk_injective (A := F) (B := F') V) hfix'

set_option backward.isDefEq.respectTransparency false in
noncomputable def CFSG.theorem_3_5_coindEquivOfNotall
    {G : Type*} [Group G] [Finite G] {H : Subgroup G} [H.Normal]
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) [Representation.IsIrreducible ρ]
    {p : ℕ} (hcardQ : Nat.card (G ⧸ H) = p) (hp : Nat.Prime p)
    (hchar : ringChar F = 0 ∨
      (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card H)))
    (M : Subrepresentation (ρ.comp H.subtype))
    [Representation.IsIrreducible M.toRepresentation]
    (hnall : ¬ ∀ x : G,
      Nonempty (M.toRepresentation ≃ₗ Theory.Representation.conjugateRep M.toRepresentation x)) :
    ρ ≃ₗ coindRep M.toRepresentation := by
  let : FiniteDimensional F V := finiteDimensional_of_irreducible_finite_group ρ inferInstance
  let : FiniteDimensional F M.toSubmodule := FiniteDimensional.of_injective M.toSubmodule.subtype
    Subtype.val_injective
  let f : ρ →ₗ coindRep M.toRepresentation := theorem_3_5_coindMapOfSubrep ρ hchar M
  let : Nontrivial M.toSubmodule := Subrepresentation.irreducible_module_nontrivial M.toRepresentation
  have hf_ne : f ≠ 0 := by
    obtain ⟨m0, hm0_ne⟩ := exists_ne (0 : M.toSubmodule)
    intro hf0
    have h_eval :
        coindEval (ρ := M.toRepresentation) (1 : G) (f m0) = m0 :=
      theorem_3_5_coindMapOfSubrep_eval_one ρ hchar M m0
    have h_zero :
        coindEval (ρ := M.toRepresentation) (1 : G) (f m0) = 0 := by
      simp [f, hf0]
    exact hm0_ne (h_eval.symm.trans h_zero)
  have hsimple_coind :
      IsSimpleOrder (Subrepresentation (coindRep (ρ := M.toRepresentation))) :=
    coindRep_irreducible_of_notall (ρ := M.toRepresentation) hcardQ hp hnall
  let : Representation.IsIrreducible (coindRep (ρ := M.toRepresentation)) := hsimple_coind
  have hfinj : Function.Injective f := by
    rcases (Representation.IsIrreducible.injective_or_eq_zero
      (ρ := ρ) (σ := coindRep (ρ := M.toRepresentation)) (f := f)) with hfinj | hf0
    · exact hfinj
    · exact False.elim (hf_ne hf0)
  have hrange_ne : f.range ≠ ⊥ := by
    intro hbot
    apply hf_ne
    apply Theory.Representation.RepMap.toLinearMap_injective
    apply LinearMap.range_eq_bot.mp
    have hbot' := congrArg Subrepresentation.toSubmodule hbot
    change LinearMap.range f.toLinearMap =
      (⊥ : Submodule F (Representation.coindV H.subtype M.toRepresentation)) at hbot'
    exact hbot'
  have hrange_top : f.range = ⊤ := by
    rcases hsimple_coind.eq_bot_or_eq_top f.range with hbot | htop
    · exact False.elim (hrange_ne hbot)
    · exact htop
  have hfsurj : Function.Surjective f := by
    apply LinearMap.range_eq_top.mp
    have hrange_top' := congrArg Subrepresentation.toSubmodule hrange_top
    change LinearMap.range f.toLinearMap =
      (⊤ : Submodule F (Representation.coindV H.subtype M.toRepresentation)) at hrange_top'
    exact hrange_top'
  let eLin : V ≃ₗ[F] Representation.coindV H.subtype M.toRepresentation :=
    LinearEquiv.ofBijective f.toLinearMap ⟨hfinj, hfsurj⟩
  refine Theory.Representation.RepEquiv.mk eLin ?_
  intro g
  ext v x
  simpa [LinearMap.comp_apply, eLin] using congrArg
    (fun z : Representation.coindV H.subtype M.toRepresentation => z.1 x)
    (Representation.IntertwiningMap.isIntertwining
      (ρ := ρ) (σ := coindRep (ρ := M.toRepresentation)) f g v)

theorem CFSG.theorem_3_5_distinct_constituents_case
    {G : Type*} [Group G] [Finite G] {F : Type*} [Field F] {V : Type*}
    [AddCommGroup V] [Module F V]
    (K R : Subgroup G) [K.Normal] (ρ : Representation F G V)
    [Representation.IsIrreducible ρ]
    (hfrob : IsFrobeniusGroupWithKernelComplement K R)
    (hR_prime : Nat.Prime (Nat.card R))
    (hchar : ringChar F = 0 ∨
      (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card G)))
    (hfixR : Module.rank F ↥(ρ.fixedSubspace R) = 1)
    (M : Subrepresentation (ρ.comp K.subtype))
    [Representation.IsIrreducible M.toRepresentation]
    (hnall : ¬ ∀ x : G,
      Nonempty (M.toRepresentation ≃ₗ Theory.Representation.conjugateRep M.toRepresentation x)) :
    ⁅K, K⁆ ≤ ρ.ker := by
  let : FiniteDimensional F V := finiteDimensional_of_irreducible_finite_group ρ inferInstance
  let : FiniteDimensional F M.toSubmodule := FiniteDimensional.of_injective M.toSubmodule.subtype
    Subtype.val_injective
  have hcardQ : Nat.card (G ⧸ K) = Nat.card R := by
    calc
      Nat.card (G ⧸ K) = K.index := by simpa using K.index_eq_card.symm
      _ = Nat.card R := hfrob.isComplement'.symm.index_eq_card
  have hcharK :
      ringChar F = 0 ∨
        (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card K)) := by
    exact hchar_of_card_dvd (G := G) (F := F) hchar (Subgroup.card_subgroup_dvd_card K)
  let e : ρ ≃ₗ coindRep M.toRepresentation :=
    theorem_3_5_coindEquivOfNotall (ρ := ρ) hcardQ hR_prime hcharK M hnall
  let : FiniteDimensional F (Representation.coindV K.subtype M.toRepresentation) :=
    e.toLinearEquiv.finiteDimensional
  have hfixR_finrank : Module.finrank F ↥(ρ.fixedSubspace R) = 1 := by
    exact
      (Module.rank_eq_one_iff_finrank_eq_one (R := F) (M := ↥(ρ.fixedSubspace R))).mp hfixR
  have hfix_coind_finrank :
      Module.finrank F ↥((coindRep (ρ := M.toRepresentation)).fixedSubspace R) = 1 := by
    let eFix := theorem_3_5_fixedSubspace_equiv_of_equiv e R
    calc
      Module.finrank F ↥((coindRep (ρ := M.toRepresentation)).fixedSubspace R)
          = Module.finrank F ↥(ρ.fixedSubspace R) := by
            simpa using (LinearEquiv.finrank_eq eFix.symm)
      _ = 1 := hfixR_finrank
  let FixEval :
      ↥((coindRep (ρ := M.toRepresentation)).fixedSubspace R) →ₗ[F] M.toSubmodule :=
    (coindEval (ρ := M.toRepresentation) (1 : G)).toLinearMap.comp
      ((coindRep (ρ := M.toRepresentation)).fixedSubspace R).subtype
  have hFixEval_surj : Function.Surjective FixEval := by
    simpa [FixEval] using
      theorem_3_5_coindEval_surjective_fixedSubspace
        (ρ := M.toRepresentation) hfrob.isComplement'
  have hM_finrank_le : Module.finrank F M.toSubmodule ≤ 1 := by
    have hrange_top : LinearMap.range FixEval = ⊤ := LinearMap.range_eq_top.2 hFixEval_surj
    calc
      Module.finrank F M.toSubmodule = Module.finrank F (LinearMap.range FixEval) := by
        rw [hrange_top]
        simp
      _ ≤ Module.finrank F ↥((coindRep (ρ := M.toRepresentation)).fixedSubspace R) :=
        LinearMap.finrank_range_le FixEval
      _ = 1 := hfix_coind_finrank
  let : Nontrivial M.toSubmodule := Subrepresentation.irreducible_module_nontrivial M.toRepresentation
  have hM_finrank : Module.finrank F M.toSubmodule = 1 := by
    have hM_finrank_pos : 0 < Module.finrank F M.toSubmodule :=
      Module.finrank_pos_iff.mpr inferInstance
    exact le_antisymm hM_finrank_le (Nat.succ_le_of_lt hM_finrank_pos)
  have hcommM : commutator ↥K ≤ M.toRepresentation.ker :=
    theorem_3_5_commutator_le_ker_of_finrank_one
      (ρ := M.toRepresentation) hM_finrank
  have hcomm_subgroupOf : ⁅K, K⁆.subgroupOf K ≤ M.toRepresentation.ker := by
    intro x hx
    have hx_comm : x ∈ commutator ↥K := by
      rw [← Subgroup.mem_map_iff_mem K.subtype_injective, Subgroup.map_subtype_commutator]
      simpa [Subgroup.mem_subgroupOf] using hx
    exact hcommM hx_comm
  have hcoind_ker : ⁅K, K⁆ ≤ (coindRep (ρ := M.toRepresentation)).ker :=
    theorem_3_5_le_ker_coind_of_le_ker
      (ρ := M.toRepresentation) (N := ⁅K, K⁆)
      (show ⁅K, K⁆ ≤ K by
        simpa using (Subgroup.commutator_le_right (H₁ := K) (H₂ := K))) hcomm_subgroupOf
  exact theorem_3_5_le_ker_of_equiv e hcoind_ker

theorem CFSG.theorem_3_5_irreducible_restriction_of_all_conjugates
    {G : Type*} [Group G] [Finite G] {F : Type*} [Field F] [IsAlgClosed F]
    {V : Type*} [AddCommGroup V] [Module F V]
    (K R : Subgroup G) [K.Normal] (ρ : Representation F G V)
    [Representation.IsIrreducible ρ]
    (hfrob : IsFrobeniusGroupWithKernelComplement K R)
    (hR_prime : Nat.Prime (Nat.card R))
    (M : Subrepresentation (ρ.comp K.subtype))
    [Representation.IsIrreducible M.toRepresentation]
    (hall : ∀ x : G,
      Nonempty (M.toRepresentation ≃ₗ Theory.Representation.conjugateRep M.toRepresentation x)) :
    Representation.IsIrreducible (ρ.comp K.subtype) := by
  let : FiniteDimensional F V := finiteDimensional_of_irreducible_finite_group ρ inferInstance
  let : FiniteDimensional F M.toSubmodule := FiniteDimensional.of_injective M.toSubmodule.subtype
    Subtype.val_injective
  have hcardQ : Nat.card (G ⧸ K) = Nat.card R := by
    calc
      Nat.card (G ⧸ K) = K.index := by simpa using K.index_eq_card.symm
      _ = Nat.card R := hfrob.isComplement'.symm.index_eq_card
  let : Fact (Nat.Prime (Nat.card R)) := ⟨hR_prime⟩
  have hcycQ : IsCyclic (G ⧸ K) := isCyclic_of_prime_card (α := G ⧸ K) hcardQ
  let hE : ∀ x : G, M.toRepresentation ≃ₗ Theory.Representation.conjugateRep M.toRepresentation x :=
    fun x => Classical.choice (hall x)
  have hM : M.toRepresentation ≃ₗ M.toRepresentation := by
    simpa using (Theory.Representation.RepEquiv.refl M.toRepresentation)
  let eρK : ρ.comp K.subtype ≃ₗ M.toRepresentation :=
    proposition_2_2_a
      (G := G) (H := K) hcycQ M.toRepresentation hE
      (ι := ρ) (φ := M) hM
  exact (Theory.Representation.RepEquiv.irreducible_euqiv (f := eρK)).2 inferInstance

theorem CFSG.theorem_3_5_K_module_branch
    {G : Type*} [Group G] [Finite G] {F : Type*} [Field F] [IsAlgClosed F]
    {V : Type*} [AddCommGroup V] [Module F V]
    (K R : Subgroup G) [K.Normal] (ρ : Representation F G V)
    [Representation.IsIrreducible ρ]
    (hfrob : IsFrobeniusGroupWithKernelComplement K R)
    (hR_prime : Nat.Prime (Nat.card R))
    (hchar : ringChar F = 0 ∨
      (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card G)))
    (hfixR : Module.rank F ↥(ρ.fixedSubspace R) = 1) :
    Representation.IsIrreducible (ρ.comp K.subtype) ∨ ⁅K, K⁆ ≤ ρ.ker := by
  let : FiniteDimensional F V := finiteDimensional_of_irreducible_finite_group ρ inferInstance
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨M, hMirr⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
    (ρ.comp K.subtype)
  let : Representation.IsIrreducible M.toRepresentation := hMirr
  by_cases hnall : ¬ ∀ x : G,
      Nonempty (M.toRepresentation ≃ₗ Theory.Representation.conjugateRep M.toRepresentation x)
  · right
    exact theorem_3_5_distinct_constituents_case K R ρ hfrob hR_prime hchar hfixR M hnall
  · left
    exact theorem_3_5_irreducible_restriction_of_all_conjugates K R ρ hfrob hR_prime M
      (not_not.mp hnall)

public theorem CFSG.theorem_3_5_coprime_card_of_prime_complement
    {G : Type*} [Group G] [Finite G] (K R : Subgroup G)
    (hfrob : IsFrobeniusGroupWithKernelComplement K R)
    (hR_prime : Nat.Prime (Nat.card R)) :
    Nat.Coprime (Nat.card K) (Nat.card R) := by
  classical
  let : K.Normal := hfrob.normal
  let p := Nat.card R
  have hp : Nat.Prime p := by
    simpa [p] using hR_prime
  refine Nat.Coprime.symm ((hp.coprime_iff_not_dvd).2 ?_)
  intro hpdvdK
  have hK_ne : K ≠ ⊥ := by
    intro hK_bot
    have hzero : Nat.card K = 1 := (Subgroup.eq_bot_iff_card (H := K)).1 hK_bot
    exact hp.not_dvd_one (hzero ▸ hpdvdK)
  have hR_ne : R ≠ ⊥ := by
    intro hR_bot
    exact hR_prime.ne_one ((Subgroup.eq_bot_iff_card (H := R)).1 hR_bot)
  have hcentK :
      ∀ x : R, x ≠ 1 → elementCentralizerIn K (x : G) = ⊥ :=
    (lemma_3_1 (K := K) (R := R) hK_ne hR_ne hfrob.normal hfrob.isComplement').1 hfrob
  let p' := p
  have hp' : Nat.Prime p' := hp
  let : Fact p'.Prime := ⟨hp'⟩
  have hRK : R ≤ Subgroup.normalizer K := Subgroup.le_normalizer_of_normal (H := K)
  have : Subgroup.Normalizes R K := ⟨hRK⟩
  have hRp : IsPGroup p' ↥R := by
    refine (IsPGroup.iff_card (p := p') (G := ↥R)).2 ?_
    refine ⟨1, ?_⟩
    simp [p', p]
  have hpSylow : ¬ p' ∣ Nat.card (Sylow p' ↥K) := by
    simpa using (not_dvd_card_sylow (p := p') (G := ↥K))
  obtain ⟨P, hPfix⟩ :=
    hRp.nonempty_fixed_point_of_prime_not_dvd_card (Sylow p' ↥K) hpSylow
  have hPinv : IsInvariant (↥R) (↥K) (P : Subgroup ↥K) := by
    refine ⟨?_⟩
    intro a g
    constructor
    · intro hg
      have hsmulP : a • (P : Subgroup ↥K) = (P : Subgroup ↥K) := by
        have hfixed := congrArg (fun Q : Sylow p' ↥K => (Q : Subgroup ↥K))
          ((MulAction.mem_fixedPoints.mp hPfix) a)
        change a • (P : Subgroup ↥K) = (P : Subgroup ↥K) at hfixed
        exact hfixed
      have : a • g ∈ a • (P : Subgroup ↥K) :=
        Subgroup.smul_mem_pointwise_smul g a (P : Subgroup ↥K) hg
      simpa [hsmulP] using this
    · intro hg
      have hsmulPinv : a⁻¹ • (P : Subgroup ↥K) = (P : Subgroup ↥K) := by
        have hfixed := congrArg (fun Q : Sylow p' ↥K => (Q : Subgroup ↥K))
          ((MulAction.mem_fixedPoints.mp hPfix) a⁻¹)
        change a⁻¹ • (P : Subgroup ↥K) = (P : Subgroup ↥K) at hfixed
        exact hfixed
      have : a⁻¹ • (a • g) ∈ a⁻¹ • (P : Subgroup ↥K) :=
        Subgroup.smul_mem_pointwise_smul (a • g) a⁻¹ (P : Subgroup ↥K) hg
      simpa [hsmulPinv, inv_smul_smul] using this
  have hP_ne_bot : (P : Subgroup ↥K) ≠ ⊥ := by
    exact P.ne_bot_of_dvd_card hpdvdK
  have hPp : IsPGroup p' ↥(P : Subgroup ↥K) := P.isPGroup'
  have hpP_dvd : p' ∣ Nat.card ↥(P : Subgroup ↥K) := by
    rcases hPp.card_eq_or_dvd with h1 | h2
    · exact False.elim (hP_ne_bot ((Subgroup.eq_bot_iff_card (H := (P : Subgroup ↥K))).2 h1))
    · exact h2
  have h1fix :
      (1 : (P : Subgroup ↥K)) ∈ MulAction.fixedPoints (↥R) ↥(P : Subgroup ↥K) := by
    simp [MulAction.mem_fixedPoints]
  obtain ⟨x, hxfix, hxne⟩ :=
    hRp.exists_fixed_point_of_prime_dvd_card_of_fixed_point
      (α := ↥(P : Subgroup ↥K)) hpP_dvd h1fix
  have hR_nontrivial : Nontrivial ↥R := R.nontrivial_iff_ne_bot.mpr hR_ne
  obtain ⟨r, hr_ne⟩ := exists_ne (1 : R)
  have hxr : r • x = x := (MulAction.mem_fixedPoints.mp hxfix) r
  have hx_central : x.1.1 ∈ elementCentralizerIn K (r : G) := by
    refine ⟨x.1.2, ?_⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hxrK : r • (x : ↥K) = x := congrArg Subtype.val hxr
    have hxrG : (((r • (x : ↥K)) : ↥K) : G) = (x : ↥K) := congrArg Subtype.val hxrK
    have hconj : (r : G) * (x.1.1 : G) * (r : G)⁻¹ = x.1.1 := by
      simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hRK] using hxrG
    have hmul := congrArg (fun t : G => t * (r : G)) hconj
    simpa [mul_assoc] using hmul.symm
  have hx_one : (x.1.1 : G) = 1 := by
    have hxbot : (x.1.1 : G) ∈ (⊥ : Subgroup G) := by
      rw [hcentK r hr_ne] at hx_central
      simpa using hx_central
    simpa using hxbot
  apply hxne
  apply Subtype.ext
  apply Subtype.ext
  exact hx_one.symm

theorem CFSG.theorem_3_5_commutator_subgroup_le_ker_of_finrank_one
    {G : Type*} [Group G] {F : Type*} [Field F] {V : Type*}
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (K : Subgroup G) [K.Normal] (ρ : Representation F G V) (hfin : Module.finrank F V = 1) :
    ⁅K, K⁆ ≤ ρ.ker := by
  have hcomm : commutator ↥K ≤ (ρ.comp K.subtype).ker :=
    theorem_3_5_commutator_le_ker_of_finrank_one (ρ := ρ.comp K.subtype) hfin
  have hcomm_subgroupOf : ⁅K, K⁆.subgroupOf K ≤ (ρ.comp K.subtype).ker := by
    intro x hx
    have hx_comm : x ∈ commutator ↥K := by
      rw [← Subgroup.mem_map_iff_mem K.subtype_injective, Subgroup.map_subtype_commutator]
      simpa [Subgroup.mem_subgroupOf] using hx
    exact hcomm hx_comm
  intro x hx
  change (⟨x, (Subgroup.commutator_le_right (H₁ := K) (H₂ := K)) hx⟩ : K) ∈
      (ρ.comp K.subtype).ker
  have hx' :
      (⟨x, (Subgroup.commutator_le_right (H₁ := K) (H₂ := K)) hx⟩ : K) ∈
        ⁅K, K⁆.subgroupOf K := by
    simp [Subgroup.mem_subgroupOf, hx]
  exact hcomm_subgroupOf hx'

theorem CFSG.theorem_3_5_subgroupOfSup_frobenius_of_invariant
    {G : Type*} [Group G] [Finite G] (K R N : Subgroup G) [K.Normal]
    (hfrob : IsFrobeniusGroupWithKernelComplement K R)
    (hN_ne : N ≠ ⊥) (hR_ne : R ≠ ⊥) (hN_le : N ≤ K)
    (hRinv : ∀ r : R, ∀ n ∈ N, (r : G) * n * (r : G)⁻¹ ∈ N) :
    IsFrobeniusGroupWithKernelComplement (N.subgroupOf (N ⊔ R)) (R.subgroupOf (N ⊔ R)) := by
  let S : Subgroup G := N ⊔ R
  have hK_ne : K ≠ ⊥ := by
    intro hK_bot
    exact hN_ne (le_antisymm (fun x hx => by simpa [hK_bot] using hN_le hx) bot_le)
  have hcentK :
      ∀ x : R, x ≠ 1 → elementCentralizerIn K (x : G) = ⊥ :=
    (lemma_3_1 (K := K) (R := R) hK_ne hR_ne hfrob.normal hfrob.isComplement').1 hfrob
  have hRnormN : R ≤ Subgroup.normalizer N := by
    intro r hr
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact hRinv ⟨r, hr⟩ n hn
    · intro hn
      have hrinv : ((⟨r, hr⟩ : R)⁻¹ : R) = ⟨(r : G)⁻¹, R.inv_mem hr⟩ := rfl
      have hconj :=
        hRinv ((⟨r, hr⟩ : R)⁻¹) ((r : G) * n * (r : G)⁻¹) hn
      simpa [hrinv, mul_assoc] using hconj
  have hNsub_normal : (N.subgroupOf S).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    exact sup_le Subgroup.le_normalizer hRnormN
  have hNsub_ne : N.subgroupOf S ≠ ⊥ := by
    intro hbot
    apply hN_ne
    have hcard :
        Nat.card (N.subgroupOf S) = 1 :=
      (Subgroup.eq_bot_iff_card (H := N.subgroupOf S)).1 hbot
    have hcardN : Nat.card N = 1 := by
      rw [natCard_subgroupOf_eq N S le_sup_left] at hcard
      exact hcard
    exact (Subgroup.eq_bot_iff_card (H := N)).2 hcardN
  have hRsub_ne : R.subgroupOf S ≠ ⊥ := by
    intro hbot
    apply hR_ne
    have hcard :
        Nat.card (R.subgroupOf S) = 1 :=
      (Subgroup.eq_bot_iff_card (H := R.subgroupOf S)).1 hbot
    have hcardR : Nat.card R = 1 := by
      rw [natCard_subgroupOf_eq R S le_sup_right] at hcard
      exact hcard
    exact (Subgroup.eq_bot_iff_card (H := R)).2 hcardR
  have hsub_frob :
      IsFrobeniusGroupWithKernelComplement (N.subgroupOf S) (R.subgroupOf S) := by
    have hdisj : Disjoint N R := hfrob.isComplement'.disjoint.mono_left hN_le
    have hsub_compl :
        (N.subgroupOf S).IsComplement' (R.subgroupOf S) := by
      have htop : N.subgroupOf S ⊔ R.subgroupOf S = ⊤ := by
        calc
          N.subgroupOf S ⊔ R.subgroupOf S = (N ⊔ R).subgroupOf S := by
            symm
            simpa [S] using
              (Subgroup.subgroupOf_sup (A := N) (A' := R) (B := S) le_sup_left le_sup_right)
          _ = ⊤ := by
            apply (Subgroup.subgroupOf_eq_top).2
            simp [S]
      refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
      · rw [Subgroup.disjoint_def]
        intro x hxN hxR
        apply Subtype.ext
        exact (Subgroup.disjoint_def.mp hdisj) hxN hxR
      · rw [Set.eq_univ_iff_forall]
        intro x
        have hxsup : x ∈ N.subgroupOf S ⊔ R.subgroupOf S := by
          rw [htop]
          trivial
        rcases (Subgroup.mem_sup_of_normal_left (x := x) (s := N.subgroupOf S)
          (t := R.subgroupOf S)).1 hxsup with ⟨n, hnN, r, hrR, hnr⟩
        refine ⟨n, hnN, r, hrR, ?_⟩
        simpa using hnr
    refine
      (lemma_3_1 (G := S) (K := N.subgroupOf S) (R := R.subgroupOf S)
        hNsub_ne hRsub_ne hNsub_normal hsub_compl).2 ?_
    intro x hx_ne
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    rcases hy with ⟨hyN, hyC⟩
    have hxG_ne : ((x : S) : G) ≠ 1 := by
      intro hxG_eq_one
      apply hx_ne
      apply Subtype.ext
      apply Subtype.ext
      exact hxG_eq_one
    let xR : R := ⟨((x : S) : G), x.2⟩
    have hxR_ne : xR ≠ 1 := by
      intro hxR_eq_one
      exact hxG_ne (congrArg Subtype.val hxR_eq_one)
    have hyC' : (y : G) ∈ elementCentralizerIn K (xR : G) := by
      refine ⟨hN_le hyN, ?_⟩
      have hyCommS : (y : S) * (x : S) = (x : S) * (y : S) :=
        Subgroup.mem_centralizer_singleton_iff.mp hyC
      exact
        Subgroup.mem_centralizer_singleton_iff.mpr <|
          congrArg Subtype.val hyCommS
    have hybot : (y : G) ∈ (⊥ : Subgroup G) := by
      rw [hcentK xR hxR_ne] at hyC'
      simpa using hyC'
    apply Subtype.ext
    simpa using hybot
  simpa [S] using hsub_frob

set_option maxHeartbeats 1000000 in
theorem CFSG.theorem_3_5_faithful_irreducible_endpoint
    {G : Type uG} [Group G] [Finite G] {F : Type uF} [Field F] [IsAlgClosed F]
    {V : Type uV} [AddCommGroup V] [Module F V]
    (K R : Subgroup G) [K.Normal] (ρ : Representation F G V)
    (hind : Theorem35IndHyp.{uG, uF, uV} (F := F) K)
    [Representation.IsIrreducible ρ]
    (hfrob : IsFrobeniusGroupWithKernelComplement K R) (hsolvK : Group.IsSolvable K)
    (hR_cyclic : IsCyclic R) (hR_prime : Nat.Prime (Nat.card R))
    (hchar : ringChar F = 0 ∨
      (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card G)))
    (hfixR : Module.rank F ↥(ρ.fixedSubspace R) = 1)
    (hker_bot : ρ.ker = ⊥) :
    ⁅K, K⁆ ≤ ρ.ker := by
  classical
  let C : Subgroup G := ⁅K, K⁆
  let : FiniteDimensional F V := finiteDimensional_of_irreducible_finite_group ρ inferInstance
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  let : Group.IsSolvable ↥K := hsolvK
  have hR_ne : R ≠ ⊥ := by
    intro hR_bot
    exact hR_prime.ne_one ((Subgroup.eq_bot_iff_card (H := R)).1 hR_bot)
  have hcommC : IsMulCommutative ↥C := by
    simpa [C] using
      theorem_3_5_commutator_abelian K R ρ hind hfrob hsolvK hR_cyclic hR_prime hchar hfixR
        hker_bot
  rcases theorem_3_5_K_module_branch K R ρ hfrob hR_prime hchar hfixR with hKirr | hCker
  · by_cases hCbot : C = ⊥
    · simp [C, hCbot]
    have hcomm_lt : C < K := by
      have hK_ne : K ≠ ⊥ := by
        intro hK_bot
        exact hCbot (by simp [C, hK_bot])
      let : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).2 hK_ne
      have hlt' : commutator ↥K < (⊤ : Subgroup ↥K) :=
        Group.IsSolvable.commutator_lt_top_of_nontrivial (G := ↥K)
      have htop_map : (⊤ : Subgroup ↥K).map K.subtype = K := by
        simpa [MonoidHom.range_eq_map] using (K.range_subtype : K.subtype.range = K)
      have hmap_lt :
          (commutator ↥K).map K.subtype < K := by
        have :=
          (Subgroup.map_subtype_lt_map_subtype (G' := K)
            (H := commutator ↥K) (K := (⊤ : Subgroup ↥K))).2 hlt'
        simpa [Subgroup.map_subtype_commutator, htop_map] using this
      simpa [C, Subgroup.map_subtype_commutator] using hmap_lt
    let S : Subgroup G := C ⊔ R
    let Csub : Subgroup S := C.subgroupOf S
    let Rsub : Subgroup S := R.subgroupOf S
    let ρS : Representation F S V := ρ.comp S.subtype
    have hRinvC : ∀ r : R, ∀ c ∈ C, (r : G) * c * (r : G)⁻¹ ∈ C := by
      intro r c hc
      exact (inferInstance : C.Normal).conj_mem c hc r
    have hsub_frob : IsFrobeniusGroupWithKernelComplement Csub Rsub :=
      theorem_3_5_subgroupOfSup_frobenius_of_invariant K R C hfrob
        (by simpa [C] using hCbot) hR_ne (by simpa [C] using hcomm_lt.1) hRinvC
    have hcard_sub_dvd : Nat.card S ∣ Nat.card G := Subgroup.card_subgroup_dvd_card S
    have hcharS :
        ringChar F = 0 ∨
          (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card S)) :=
      hchar_of_card_dvd (G := G) (F := F) hchar hcard_sub_dvd
    have hcharCsub :
        ringChar F = 0 ∨
          (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card Csub)) := by
      exact hchar_of_card_dvd (G := S) (F := F) hcharS (Subgroup.card_subgroup_dvd_card Csub)
    have hRsub_prime : Nat.Prime (Nat.card Rsub) := by
      rw [natCard_subgroupOf_eq R S le_sup_right]
      exact hR_prime
    by_cases hSirr : Representation.IsIrreducible ρS
    · let : Representation.IsIrreducible ρS := hSirr
      obtain ⟨L, hLirr⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
        (ρS.comp Csub.subtype)
      let : Representation.IsIrreducible L.toRepresentation := hLirr
      by_cases hall : ∀ x : S,
          Nonempty (L.toRepresentation ≃ₗ Theory.Representation.conjugateRep L.toRepresentation x)
      · have hCirr : Representation.IsIrreducible (ρS.comp Csub.subtype) :=
          theorem_3_5_irreducible_restriction_of_all_conjugates Csub Rsub ρS hsub_frob
            hRsub_prime L hall
        let : Representation.IsIrreducible (ρS.comp Csub.subtype) := hCirr
        have hfin : Module.finrank F V = 1 := by
          simpa using
            (Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative
              (ρ := ρS.comp Csub.subtype))
        exact theorem_3_5_commutator_subgroup_le_ker_of_finrank_one K ρ hfin
      · have hcardQ : Nat.card (S ⧸ Csub) = Nat.card R := by
          calc
            Nat.card (S ⧸ Csub) = Csub.index := by simpa using Csub.index_eq_card.symm
            _ = Nat.card Rsub := hsub_frob.2.1.symm.index_eq_card
            _ = Nat.card R := by rw [natCard_subgroupOf_eq R S le_sup_right]
        let e : ρS ≃ₗ coindRep L.toRepresentation :=
          theorem_3_5_coindEquivOfNotall (ρ := ρS) hcardQ hR_prime hcharCsub L hall
        have hLfin : Module.finrank F L.toSubmodule = 1 := by
          simpa using
            (Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative
              (ρ := L.toRepresentation))
        let : Fintype (S ⧸ Csub) := Fintype.ofFinite (S ⧸ Csub)
        have hcardQ' : Fintype.card (S ⧸ Csub) = Nat.card R := by
          simpa [Nat.card_eq_fintype_card] using hcardQ
        have hdim : Module.finrank F V = Nat.card R := by
          calc
            Module.finrank F V =
                Module.finrank F (Representation.coindV Csub.subtype L.toRepresentation) := by
                  simpa using (LinearEquiv.finrank_eq e.toLinearEquiv)
            _ = Fintype.card (S ⧸ Csub) * Module.finrank F L.toSubmodule := by
                  simpa using (finrank_coindRep_eq_card_mul (ρ := L.toRepresentation))
            _ = Nat.card R := by rw [hcardQ', hLfin, Nat.mul_one]
        let : Representation.IsIrreducible (ρ.comp K.subtype) := hKirr
        let : Theory.Representation.IsAbsolutelyIrreducible (ρ.comp K.subtype) :=
          (Theory.Representation.isAbsolutelyIrreducible_iff_surjective (ρ := ρ.comp K.subtype)).2
            (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
              (ρ := ρ.comp K.subtype)).surjective
        have hdim_dvd : Module.finrank F V ∣ Nat.card K :=
          lemma_2_3 (ρ := ρ.comp K.subtype)
        have hcopKR : Nat.Coprime (Nat.card K) (Nat.card R) :=
          theorem_3_5_coprime_card_of_prime_complement K R hfrob hR_prime
        have hR_dvd : Nat.card R ∣ Nat.card K := by
          rw [← hdim]
          exact hdim_dvd
        exact False.elim ((hR_prime.coprime_iff_not_dvd.mp hcopKR.symm) hR_dvd)
    · have hρScr : ρS.IsCompletelyReducible := by
        exact
          Representation.isCompletelyReducible_of_ringChar_eq_zero_or_prime_coprime
            (ρ := ρS) hcharS
      let : ComplementedLattice (Subrepresentation ρS) := by
        exact
          (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule
            (ρ := ρS)).2 hρScr
      obtain ⟨P, hPirr⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional ρS
      let : Representation.IsIrreducible P.toRepresentation := hPirr
      have hP_top_ne : P ≠ ⊤ := by
        intro hP_top
        subst hP_top
        let eTop : (⊤ : Subrepresentation ρS).toRepresentation ≃ₗ ρS := by
          refine Theory.Representation.RepEquiv.mk (Submodule.topEquiv : (⊤ : Submodule F V) ≃ₗ[F] V) ?_
          intro g
          ext v
          rfl
        exact hSirr ((Theory.Representation.RepEquiv.irreducible_euqiv (f := eTop)).1 hPirr)
      let Q : Subrepresentation ρS := Classical.choose (exists_isCompl P)
      have hcompl : IsCompl P Q := Classical.choose_spec (exists_isCompl P)
      have hcompl_sub : IsCompl P.toSubmodule Q.toSubmodule := by
        refine ⟨?_, ?_⟩
        · rw [disjoint_iff]
          have h := congrArg Subrepresentation.toSubmodule hcompl.inf_eq_bot
          change P.toSubmodule ⊓ Q.toSubmodule = (⊥ : Submodule F V) at h
          exact h
        · rw [codisjoint_iff]
          have h := congrArg Subrepresentation.toSubmodule hcompl.sup_eq_top
          change P.toSubmodule ⊔ Q.toSubmodule = (⊤ : Submodule F V) at h
          exact h
      have hP_ne_bot : P.toSubmodule ≠ ⊥ := by
        let : Nontrivial P.toSubmodule := Subrepresentation.irreducible_module_nontrivial P.toRepresentation
        exact Submodule.nontrivial_iff_ne_bot.mp inferInstance
      have hQ_ne_bot : Q.toSubmodule ≠ ⊥ := by
        intro hQ_bot
        exact hP_top_ne (by
          apply Subrepresentation.toSubmodule_injective
          simpa [hQ_bot] using congrArg Subrepresentation.toSubmodule hcompl.sup_eq_top)
      let eFix := theorem_3_5_fixedSubspace_prodEquivOfIsCompl (ρ := ρS) P Q hcompl_sub Rsub
      have hfixS : Module.rank F ↥(ρS.fixedSubspace Rsub) = 1 := by
        rw [fixedSubspace_subgroupOf_eq (ρ := ρ) (S := S) (R := R) le_sup_right]
        exact hfixR
      have hfixS_fin :
          Module.finrank F ↥(ρS.fixedSubspace Rsub) = 1 :=
        (Module.rank_eq_one_iff_finrank_eq_one (R := F) (M := ↥(ρS.fixedSubspace Rsub))).mp hfixS
      by_cases hPfix : P.toRepresentation.fixedSubspace Rsub = ⊥
      · have hC_P : Csub ≤ P.toRepresentation.ker := by
          by_contra hCnle
          exact (lemma_3_3 Csub Rsub P.toRepresentation hsub_frob hcharCsub hCnle) hPfix
        have hP_le_fix : P.toSubmodule ≤ ρS.fixedSubspace Csub := by
          intro v hv
          rw [Representation.fixedSubspace, Representation.mem_invariants]
          intro c
          have hc : ((c : Csub) : S) ∈ P.toRepresentation.ker := hC_P c.property
          rw [MonoidHom.mem_ker] at hc
          have hcv : P.toRepresentation ((c : Csub) : S) ⟨v, hv⟩ = ⟨v, hv⟩ :=
            DFunLike.congr_fun hc ⟨v, hv⟩
          have hcv' := congrArg Subtype.val hcv
          change ρS ((c : Csub) : S) v = v at hcv'
          exact hcv'
        have hfixC_neS : ρS.fixedSubspace Csub ≠ ⊥ := by
          intro hbot
          apply hP_ne_bot
          apply le_antisymm
          · intro v hv
            have hvfix : v ∈ ρS.fixedSubspace Csub := hP_le_fix hv
            simpa [hbot] using hvfix
          · exact bot_le
        have hfixC_eq : ρS.fixedSubspace Csub = ρ.fixedSubspace C :=
          fixedSubspace_subgroupOf_eq (ρ := ρ) (S := S) (R := C) le_sup_left
        have hfixC_ne : ρ.fixedSubspace C ≠ ⊥ := by
          rw [← hfixC_eq]
          exact hfixC_neS
        exact theorem_3_5_le_ker_of_normal_fixedSubspace_ne_bot (ρ := ρ) C hfixC_ne
      · have hQfix : Q.toRepresentation.fixedSubspace Rsub = ⊥ := by
          by_contra hQfix_ne
          let Pfix := P.toRepresentation.fixedSubspace Rsub
          let Qfix := Q.toRepresentation.fixedSubspace Rsub
          have hsum : Module.finrank F ↥Pfix + Module.finrank F ↥Qfix = 1 := by
            calc
              Module.finrank F ↥Pfix + Module.finrank F ↥Qfix
                  = Module.finrank F (↥Pfix × ↥Qfix) := by
                    symm
                    simp
              _ = Module.finrank F ↥(ρS.fixedSubspace Rsub) := by
                    symm
                    simpa [eFix, Pfix, Qfix] using (LinearEquiv.finrank_eq eFix)
              _ = 1 := hfixS_fin
          have hPpos : 0 < Module.finrank F ↥Pfix := by
            exact Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hPfix)
          have hQpos : 0 < Module.finrank F ↥Qfix := by
            exact Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hQfix_ne)
          omega
        have hC_Q : Csub ≤ Q.toRepresentation.ker := by
          by_contra hCnle
          exact (lemma_3_3 Csub Rsub Q.toRepresentation hsub_frob hcharCsub hCnle) hQfix
        have hQ_le_fix : Q.toSubmodule ≤ ρS.fixedSubspace Csub := by
          intro v hv
          rw [Representation.fixedSubspace, Representation.mem_invariants]
          intro c
          have hc : ((c : Csub) : S) ∈ Q.toRepresentation.ker := hC_Q c.property
          rw [MonoidHom.mem_ker] at hc
          have hcv : Q.toRepresentation ((c : Csub) : S) ⟨v, hv⟩ = ⟨v, hv⟩ :=
            DFunLike.congr_fun hc ⟨v, hv⟩
          have hcv' := congrArg Subtype.val hcv
          change ρS ((c : Csub) : S) v = v at hcv'
          exact hcv'
        have hfixC_neS : ρS.fixedSubspace Csub ≠ ⊥ := by
          intro hbot
          apply hQ_ne_bot
          apply le_antisymm
          · intro v hv
            have hvfix : v ∈ ρS.fixedSubspace Csub := hQ_le_fix hv
            simpa [hbot] using hvfix
          · exact bot_le
        have hfixC_eq : ρS.fixedSubspace Csub = ρ.fixedSubspace C :=
          fixedSubspace_subgroupOf_eq (ρ := ρ) (S := S) (R := C) le_sup_left
        have hfixC_ne : ρ.fixedSubspace C ≠ ⊥ := by
          rw [← hfixC_eq]
          exact hfixC_neS
        exact theorem_3_5_le_ker_of_normal_fixedSubspace_ne_bot (ρ := ρ) C hfixC_ne
  · exact hCker

theorem CFSG.theorem_3_5_algClosed_by_card {F : Type uF} [Field F] [IsAlgClosed F] {V : Type uV}
    [AddCommGroup V] [Module F V] :
    ∀ (G : Type uG) [Group G] [Finite G] (K R : Subgroup G) (ρ : Representation F G V),
      IsFrobeniusGroupWithKernelComplement K R →
      Group.IsSolvable K →
      IsCyclic R →
      Nat.Prime (Nat.card R) →
      (ringChar F = 0 ∨
        (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card G))) →
      Module.rank F ↥(ρ.fixedSubspace R) = 1 →
      ⁅K, K⁆ ≤ ρ.centralizerIn K := by
  let P : ℕ → Prop := fun n =>
    ∀ (W : Type uV) [AddCommGroup W] [Module F W]
      (G : Type uG) [Group G] [Finite G] (K R : Subgroup G) (ρ : Representation F G W),
      Nat.card K = n →
      IsFrobeniusGroupWithKernelComplement K R →
      Group.IsSolvable K →
      IsCyclic R →
      Nat.Prime (Nat.card R) →
      (ringChar F = 0 ∨
        (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card G))) →
      Module.rank F ↥(ρ.fixedSubspace R) = 1 →
      ⁅K, K⁆ ≤ ρ.centralizerIn K
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih W _ _ G _ _ K R ρ hcard hfrob hsolvK hR_cyclic hR_prime hchar hfixR
    have hind : Theorem35IndHyp.{uG, uF, uV} (F := F) K := by
      intro W' _ _ G' _ _ K' R' ρ' hlt hfrob' hsolvK' hR_cyclic' hR_prime' hchar' hfixR'
      have hlt' : Nat.card K' < n := by
        simpa [hcard] using hlt
      exact
        ih (Nat.card K') hlt' W' G' K' R' ρ' rfl hfrob' hsolvK' hR_cyclic' hR_prime'
          hchar' hfixR'
    by_contra hbad
    let moduleρ : Module (MonoidAlgebra F G) ρ.asModule :=
      Representation.instModuleMonoidAlgebraAsModule (ρ := ρ)
    have semisimpleρ :
        @IsSemisimpleModule (MonoidAlgebra F G) inferInstance ρ.asModule inferInstance moduleρ :=
      by
        exact
          Representation.isCompletelyReducible_of_ringChar_eq_zero_or_prime_coprime
            (ρ := ρ) hchar
    let := moduleρ
    let := semisimpleρ
    have hred :=
      theorem_3_5_faithful_reduction K R ρ hind hfrob hsolvK hR_cyclic hR_prime hchar
        hfixR hbad
    rcases hred with ⟨m, hm_simple, hmprops⟩
    let ρm := (Subrepresentation.ofSubmodule' m).toRepresentation
    dsimp at hmprops
    rcases hmprops with ⟨hfixm, hker_bot, hbadm⟩
    let : K.Normal := hfrob.normal
    have : Representation.IsIrreducible ρm :=
      irreducible_of_ofSubmodule'_simple (ρ := ρ) hm_simple
    have hcomm_ker : ⁅K, K⁆ ≤ ρm.ker :=
      theorem_3_5_faithful_irreducible_endpoint K R ρm hind hfrob hsolvK hR_cyclic hR_prime
        hchar hfixm hker_bot
    exact hbadm hcomm_ker
  intro G _ _ K R ρ hfrob hsolvK hR_cyclic hR_prime hchar hfixR
  exact hP (Nat.card K) V G K R ρ rfl hfrob hsolvK hR_cyclic hR_prime hchar hfixR

public theorem CFSG.theorem_3_5 {G : Type*} [Group G] [Finite G] {F : Type*} [Field F]
    {V : Type*}
    [AddCommGroup V] [Module F V] (K R : Subgroup G) (ρ : Representation F G V)
    (hfrob : IsFrobeniusGroupWithKernelComplement K R) (hsolvK : Group.IsSolvable K)
    (hR_cyclic : IsCyclic R) (hR_prime : Nat.Prime (Nat.card R))
    (hchar : ringChar F = 0 ∨
      (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card G)))
    (hfixR : Module.rank F ↥(ρ.fixedSubspace R) = 1) :
    ⁅K, K⁆ ≤ ρ.centralizerIn K := by
  let : K.Normal := hfrob.normal
  let F' := AlgebraicClosure F
  have hringChar : ringChar F' = ringChar F := by
    simpa [F'] using (Algebra.ringChar_eq (K := F) (L := F')).symm
  have hchar' :
      ringChar F' = 0 ∨
        (Nat.Prime (ringChar F') ∧ Nat.Coprime (ringChar F') (Nat.card G)) := by
    cases hchar with
    | inl hchar0 =>
        left
        exact hringChar.trans hchar0
    | inr hcharp =>
        right
        constructor
        · simpa [hringChar] using hcharp.1
        · simpa [hringChar] using hcharp.2
  have hcharR :
      ringChar F = 0 ∨
        (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card R)) :=
    hchar_of_card_dvd (G := G) (F := F) hchar (Subgroup.card_subgroup_dvd_card R)
  have hcharR' :
      ringChar F' = 0 ∨
        (Nat.Prime (ringChar F') ∧ Nat.Coprime (ringChar F') (Nat.card R)) :=
    hchar_of_card_dvd (G := G) (F := F') hchar' (Subgroup.card_subgroup_dvd_card R)
  have hF : (Nat.card R : F) ≠ 0 := card_ne_zero_of_char_condition (G := R) (F := F) hcharR
  have hF' : (Nat.card R : F') ≠ 0 := card_ne_zero_of_char_condition (G := R) (F := F') hcharR'
  have hfixR' :
      Module.rank F' ↥((Theory.Representation.extendScalars F' ρ).fixedSubspace R) = 1 :=
    theorem_3_5_fixedSubspace_rank_one_extendScalars
      (ρ := ρ) (H := R) hF hF' hfixR
  have hcomm_ext :
      ⁅K, K⁆ ≤ (Theory.Representation.extendScalars F' ρ).centralizerIn K :=
    theorem_3_5_algClosed_by_card G K R (Theory.Representation.extendScalars F' ρ) hfrob hsolvK
      hR_cyclic hR_prime hchar' hfixR'
  have hker_ext : ⁅K, K⁆ ≤ (Theory.Representation.extendScalars F' ρ).ker := by
    intro x hx
    exact (hcomm_ext hx).2
  have hker : ⁅K, K⁆ ≤ ρ.ker :=
    theorem_3_5_le_ker_of_extendScalars (ρ := ρ) hker_ext
  intro x hx
  exact ⟨(Subgroup.commutator_le_right (H₁ := K) (H₂ := K)) hx, hker hx⟩
