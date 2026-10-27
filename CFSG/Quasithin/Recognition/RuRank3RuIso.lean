module

public import CFSG.Quasithin.Recognition.RuRank3RuIsoData

public section

namespace CFSG.Quasithin.RuRank3

open CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

theorem mem_ruP_of_sift
    {a : Array ℕ} {g : Equiv.Perm (Fin 4060)} (hg : Rep 4060 a g)
    (h : ruSift 4060 (ruField4060 3) ruJoinBase a = true) : g ∈ ruP := by
  rw [ruP_eq_sup, ← ruChainJoin_sub]
  exact ((ruChain_sift ruChainJoin_check.1 hg).1 h : g ∈ ruChainJoin.originalSubgroup)

@[expose] noncomputable def ruTreeElt (x : ℕ) : Equiv.Perm (Fin 4060) :=
  evalSigned [ruA0, ruA1] (ruTreeWord x)

theorem ruTreeElt_mem (x : ℕ) : ruTreeElt x ∈ ruP := by
  apply evalSigned_mem
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem rep_ruGens
    : ∀ h < 2, Rep 4060 ruGensA[h]! ([ruA0, ruA1].getD h 1) :=
  rep_pair_getD rep_ruA0 rep_ruA1

theorem rep_ruGensInv
    : ∀ h < 2, Rep 4060 ruGensInvA[h]! ([ruA0, ruA1].getD h 1)⁻¹ :=
  rep_pair_getD_inv (rep_ruInv rep_ruA0 ruBasic_check.1) (rep_ruInv rep_ruA1 ruBasic_check.2.1)

theorem rep_ruTreeElt
    {x : ℕ} (hx : x < 4060) : Rep 4060 (ruTreeArr x) (ruTreeElt x) := by
  have h := allLt_spec ruIso_check.1 hx
  rw [Bool.and_eq_true] at h
  exact rep_wordA_evalSigned rep_ruGens rep_ruGensInv _ h.1

theorem ruTreeElt_apply_zero
    (x : Fin 4060) : ruTreeElt x 0 = x := by
  have h := allLt_spec ruIso_check.1 x.2
  rw [Bool.and_eq_true, beq_iff_eq] at h
  apply Fin.ext
  rw [← rep_ruTreeElt x.2 0]
  exact h.2

theorem ruP_pretransitive
    : MulAction.IsPretransitive ruP (Fin 4060) := by
  rw [MulAction.isPretransitive_iff_base (0 : Fin 4060)]
  intro x
  exact ⟨⟨ruTreeElt x, ruTreeElt_mem x⟩, ruTreeElt_apply_zero x⟩

theorem card_ruStab_zero
    : Nat.card (MulAction.stabilizer ruP (0 : Fin 4060)) = 35942400 := by
  have h := Subgroup.card_mul_index (MulAction.stabilizer ruP (0 : Fin 4060))
  have hi : (MulAction.stabilizer ruP (0 : Fin 4060)).index = 4060 := by
    have := ruP_pretransitive
    rw [MulAction.index_stabilizer_of_transitive, Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [hi, card_ruP] at h
  have h' : Nat.card (MulAction.stabilizer ruP (0 : Fin 4060)) * 4060 = 35942400 * 4060 := by
    rw [h]
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'

@[expose] def ruB (j : Fin 1755) : Fin 4060 :=
  ⟨ruDArr[(j : ℕ)]! % 4060, Nat.mod_lt _ (by norm_num)⟩

theorem ruB_val (j : Fin 1755) : (ruB j : ℕ) = ruDArr[(j : ℕ)]! := by
  have h := allLt_spec ruIso_check.2.2.1 j.2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact Nat.mod_eq_of_lt h.1

theorem ruB_injective : Function.Injective ruB := by
  intro j j' h
  have hv : ruDArr[(j : ℕ)]! = ruDArr[(j' : ℕ)]! := by rw [← ruB_val, ← ruB_val, h]
  by_contra hne
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
  · have := allLt_spec (allLt_spec ruIso_check.2.2.2.1 j'.2) hlt
    rw [bne_iff_ne] at this
    exact this hv.symm
  · have := allLt_spec (allLt_spec ruIso_check.2.2.2.1 j.2) hlt
    rw [bne_iff_ne] at this
    exact this hv

theorem ruB_zero : ruB 0 = 1 := by
  apply Fin.ext
  rw [ruB_val]
  exact ruIso_check.2.2.2.2

@[expose] noncomputable def ruR0Gen (i : ℕ) : Equiv.Perm (Fin 4060) := permOfArr 4060 (ruR0Arr i)

theorem ruIso_gen_facts {i : ℕ} (hi : i < 4) :
    isInvA 4060 (ruR0Arr i) (invCand 4060 (ruR0Arr i)) = true ∧
    ruSift 4060 (ruField4060 3) ruJoinBase (ruR0Arr i) = true ∧ (ruR0Arr i)[0]! = 0 ∧
    ∀ j < 1755, (ruR0Arr i)[ruDArr[j]!]! = ruDArr[(titsGenArrs[i]!)[j]!]! := by
  have h := allLt_spec ruIso_check.2.1 hi
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, fun j hj => by simpa using allLt_spec h4 hj⟩

theorem rep_ruR0Gen
    {i : ℕ} (hi : i < 4) : Rep 4060 (ruR0Arr i) (ruR0Gen i) :=
  (rep_permOfArr (ruIso_gen_facts hi).1).1

theorem ruR0Gen_mem
    {i : ℕ} (hi : i < 4) : ruR0Gen i ∈ ruP :=
  mem_ruP_of_sift (rep_ruR0Gen hi) (ruIso_gen_facts hi).2.1

theorem ruR0Gen_zero {i : ℕ} (hi : i < 4) : ruR0Gen i 0 = 0 := by
  apply Fin.ext
  rw [← rep_ruR0Gen hi 0]
  exact (ruIso_gen_facts hi).2.2.1

theorem ruR0Gen_ruB
    {i : ℕ} (hi : i < 4) (j : Fin 1755) :
    ruR0Gen i (ruB j) = ruB (titsGen i j) := by
  apply Fin.ext
  rw [← rep_ruR0Gen hi (ruB j), ruB_val, ruB_val, ← titsGen_rep hi j]
  exact (ruIso_gen_facts hi).2.2.2 j j.2

@[expose] def ruDStab : Subgroup (Equiv.Perm (Fin 4060)) where
  carrier := {g | ∀ x, g x ∈ Set.range ruB ↔ x ∈ Set.range ruB}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := fun {g h} hg hh x => by
    rw [Equiv.Perm.mul_apply]
    exact (hg (h x)).trans (hh x)
  inv_mem' := fun {g} hg x => by
    rw [← hg (g⁻¹ x), perm_apply_inv]

@[expose] noncomputable def ruBEquiv : Fin 1755 ≃ Set.range ruB :=
  Equiv.ofInjective ruB ruB_injective

@[expose] noncomputable def ruResD
    : ruDStab →* Equiv.Perm (Fin 1755) :=
  (Equiv.permCongrHom ruBEquiv.symm).toMonoidHom.comp
    { toFun := fun g => (g : Equiv.Perm (Fin 4060)).subtypePerm g.2
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

theorem ruB_ruResD (g : ruDStab) (j : Fin 1755) :
    ruB (ruResD g j) = (g : Equiv.Perm (Fin 4060)) (ruB j) := by
  have e : ruResD g j =
      ruBEquiv.symm (((g : Equiv.Perm (Fin 4060)).subtypePerm g.2) (ruBEquiv j)) := rfl
  have h1 := congrArg Subtype.val (ruBEquiv.apply_symm_apply
    (((g : Equiv.Perm (Fin 4060)).subtypePerm g.2) (ruBEquiv j)))
  rw [e]
  rw [show (ruBEquiv (ruBEquiv.symm (((g : Equiv.Perm (Fin 4060)).subtypePerm g.2)
    (ruBEquiv j))) : Fin 4060) = ruB (ruBEquiv.symm (((g : Equiv.Perm (Fin 4060)).subtypePerm
      g.2) (ruBEquiv j))) from rfl] at h1
  rw [h1]
  rfl

theorem ruR0Gen_mem_DStab
    {i : ℕ} (hi : i < 4) : ruR0Gen i ∈ ruDStab := by
  intro x
  constructor
  · rintro ⟨j', hj'⟩
    refine ⟨(titsGen i)⁻¹ j', ?_⟩
    apply (ruR0Gen i).injective
    rw [← hj', ruR0Gen_ruB hi, perm_apply_inv]
  · rintro ⟨j, rfl⟩
    exact ⟨titsGen i j, (ruR0Gen_ruB hi j).symm⟩

theorem ruResD_ruR0Gen
    {i : ℕ} (hi : i < 4) :
    ruResD ⟨ruR0Gen i, ruR0Gen_mem_DStab hi⟩ = titsGen i := by
  apply Equiv.ext
  intro j
  have := ruB_ruResD ⟨ruR0Gen i, ruR0Gen_mem_DStab hi⟩ j
  rw [show ((⟨ruR0Gen i, ruR0Gen_mem_DStab hi⟩ : ruDStab) : Equiv.Perm (Fin 4060)) =
    ruR0Gen i from rfl, ruR0Gen_ruB hi] at this
  exact ruB_injective this

@[expose] noncomputable def ruQ : Subgroup (Equiv.Perm (Fin 4060)) :=
  Subgroup.closure (Set.range fun i : Fin 4 => ruR0Gen i)

@[expose] def ruR0 : Subgroup (Equiv.Perm (Fin 4060)) :=
  ruP ⊓ MulAction.stabilizer (Equiv.Perm (Fin 4060)) (0 : Fin 4060)

theorem card_ruR0
    : Nat.card ruR0 = 35942400 := by
  rw [← card_ruStab_zero]
  refine Nat.card_congr ?_
  exact
    { toFun := fun g => ⟨⟨g, g.2.1⟩, g.2.2⟩
      invFun := fun g => ⟨g.1, g.1.2, g.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem ruR0Gen_mem_stab {i : ℕ} (hi : i < 4) :
    ruR0Gen i ∈ MulAction.stabilizer (Equiv.Perm (Fin 4060)) (0 : Fin 4060) := by
  rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
  exact ruR0Gen_zero hi

theorem ruR0Gen_mem_R0
    {i : ℕ} (hi : i < 4) : ruR0Gen i ∈ ruR0 :=
  Subgroup.mem_inf.mpr ⟨ruR0Gen_mem hi, ruR0Gen_mem_stab hi⟩

theorem ruQ_le_R0
    : ruQ ≤ ruR0 := by
  rw [ruQ, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact ruR0Gen_mem_R0 i.2

theorem ruQ_le_DStab :
    ruQ ≤ ruDStab := by
  rw [ruQ, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact ruR0Gen_mem_DStab i.2

theorem ruResD_mem_titsA
    {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruQ) (hD : g ∈ ruDStab) :
    ruResD ⟨g, hD⟩ ∈ titsA := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [ruResD_ruR0Gen i.2]
    exact titsGen_mem_titsA i.2
  | one =>
    have : (⟨1, hD⟩ : ruDStab) = 1 := rfl
    rw [this, map_one]
    exact one_mem _
  | mul x y hx hy ihx ihy =>
    have hxD := ruQ_le_DStab hx
    have hyD := ruQ_le_DStab hy
    have : (⟨x * y, hD⟩ : ruDStab) = ⟨x, hxD⟩ * ⟨y, hyD⟩ := rfl
    rw [this, map_mul]
    exact mul_mem (ihx hxD) (ihy hyD)
  | inv x hx ih =>
    have hxD := ruQ_le_DStab hx
    have : (⟨x⁻¹, hD⟩ : ruDStab) = (⟨x, hxD⟩)⁻¹ := rfl
    rw [this, map_inv]
    exact inv_mem (ih hxD)

theorem titsA_le_ruResD_ruQ
    : titsA ≤ (ruQ.subgroupOf ruDStab).map ruResD := by
  rw [titsA, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  refine ⟨⟨ruR0Gen i, ruR0Gen_mem_DStab i.2⟩, ?_, ruResD_ruR0Gen i.2⟩
  show _ ∈ ruQ.subgroupOf ruDStab
  rw [Subgroup.mem_subgroupOf]
  exact Subgroup.subset_closure ⟨i, rfl⟩

theorem ruQ_eq_R0
    : ruQ = ruR0 := by
  apply Subgroup.eq_of_le_of_card_ge ruQ_le_R0
  rw [card_ruR0, ← card_titsA]
  calc Nat.card titsA ≤ Nat.card ((ruQ.subgroupOf ruDStab).map ruResD) :=
        Subgroup.card_le_of_le titsA_le_ruResD_ruQ
    _ ≤ Nat.card (ruQ.subgroupOf ruDStab) :=
        Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)
    _ = Nat.card ruQ := card_subgroupOf_eq ruQ_le_DStab

theorem ruR0_le_DStab
    : ruR0 ≤ ruDStab := by
  rw [← ruQ_eq_R0]
  exact ruQ_le_DStab

@[expose] noncomputable def ruR0Hom
    : ruR0 →* titsA :=
  (ruResD.comp (Subgroup.inclusion ruR0_le_DStab)).codRestrict titsA fun g =>
    ruResD_mem_titsA (by rw [ruQ_eq_R0]; exact g.2) _

theorem ruR0Hom_apply
    (r : ruR0) :
    ((ruR0Hom r : titsA) : Equiv.Perm (Fin 1755)) = ruResD ⟨r, ruR0_le_DStab r.2⟩ := rfl

theorem ruR0Hom_surjective
    : Function.Surjective ruR0Hom := by
  intro a
  obtain ⟨⟨q, hqD⟩, hq, hqa⟩ := titsA_le_ruResD_ruQ a.2
  have hq' : q ∈ ruQ := hq
  refine ⟨⟨q, by rw [← ruQ_eq_R0]; exact hq'⟩, Subtype.ext ?_⟩
  rw [ruR0Hom_apply]
  exact hqa

theorem ruR0Hom_bijective
    : Function.Bijective ruR0Hom := by
  rw [Nat.bijective_iff_surjective_and_card]
  exact ⟨ruR0Hom_surjective, by rw [card_ruR0, card_titsA]⟩

@[expose] noncomputable def ruR0Equiv
    : ruR0 ≃* titsA :=
  MulEquiv.ofBijective ruR0Hom ruR0Hom_bijective

theorem ruR0Equiv_ruB
    (r : ruR0) (j : Fin 1755) :
    (r : Equiv.Perm (Fin 4060)) (ruB j) = ruB ((ruR0Equiv r : Equiv.Perm (Fin 1755)) j) := by
  rw [show ((ruR0Equiv r : titsA) : Equiv.Perm (Fin 1755)) = ruResD ⟨r, ruR0_le_DStab r.2⟩
    from rfl, ruB_ruResD]

end CFSG.Quasithin.RuRank3
