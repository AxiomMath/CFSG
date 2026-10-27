module

public import CFSG.Quasithin.AppendixH.H15.CocodeTwoVec
public import CFSG.Quasithin.AppendixH.H15.CocodeTwoEven
public import CFSG.Quasithin.AppendixH.Common.OctadEnum

public section

open scoped Pointwise BigOperators symmDiff

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code

@[expose] noncomputable def oSet (o : Fin 8 → Fin 24) (x : Multiplicative (Fin 6 → ZMod 2)) :
    Finset (Fin 24) :=
  (Finset.univ.filter fun p : Fin 8 => evVec (Multiplicative.toAdd x) p ≠ 0).image o

structure PhiData {d : ℕ} {a b : Fin 24} {Γ : Subgroup S24} {V : Type} [CommGroup V]
    (O : Finset (Fin 24))
    (β : ↥(⊤ : Subgroup V) →* ↥(mathModel false d a b Γ).sec ⧸
      (mathModel false d a b Γ).ker.subgroupOf (mathModel false d a b Γ).sec) : Type where
  o : Fin 8 → Fin 24
  o_inj : Function.Injective o
  o_mem : ∀ x, x ∈ O ↔ ∃ p, o p = x
  o_zero : o 0 = a
  o_one : o 1 = b
  o_octad : IsOctad O
  φ : Multiplicative (Fin 6 → ZMod 2) →* V
  vec : ∀ x, IsVecOf (mathModel false d a b Γ) β (eY (oSet o x)) (φ x)

variable {d : ℕ} {a b : Fin 24} {O : Finset (Fin 24)} {Tr S : Finset (Finset (Fin 24))}
  {B : Finset (Fin 24)} {T₀ Γ : Subgroup S24} {V : Type} [CommGroup V] {ρ : ↥Γ →* MulAut V}
  {β : ↥(⊤ : Subgroup V) →* ↥(mathModel false d a b Γ).sec ⧸
    (mathModel false d a b Γ).ker.subgroupOf (mathModel false d a b Γ).sec}

private theorem toAdd_eY_map (g : S24) (S : Finset (Fin 24)) (i : Fin 24) :
    Multiplicative.toAdd (eY (S.map g.toEmbedding)) i = Multiplicative.toAdd (eY S) (g⁻¹ i) := by
  simp only [toAdd_eY, Finset.mem_map_equiv, Equiv.Perm.inv_def]

private theorem toAdd_eY_oSet_o {o : Fin 8 → Fin 24} (ho : Function.Injective o)
    (x : Multiplicative (Fin 6 → ZMod 2)) (p : Fin 8) :
    Multiplicative.toAdd (eY (oSet o x)) (o p) = evVec (Multiplicative.toAdd x) p := by
  rw [toAdd_eY]
  by_cases hp : evVec (Multiplicative.toAdd x) p = 0
  · have hnot : o p ∉ oSet o x := by
      intro h
      obtain ⟨q, hq, hqo⟩ := Finset.mem_image.mp h
      have hqp : q = p := ho hqo
      subst hqp
      exact (Finset.mem_filter.mp hq).2 hp
    rw [if_neg hnot, hp]
  · have hmem : o p ∈ oSet o x := by
      rw [oSet]
      exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩, rfl⟩
    rw [if_pos hmem]
    rcases h13_zmod2_cases (evVec (Multiplicative.toAdd x) p) with h0 | h1
    · exact absurd h0 hp
    · exact h1.symm

private theorem toAdd_eY_oSet_notMem {o : Fin 8 → Fin 24}
    (x : Multiplicative (Fin 6 → ZMod 2)) {i : Fin 24} (hi : ∀ p, o p ≠ i) :
    Multiplicative.toAdd (eY (oSet o x)) i = 0 := by
  rw [toAdd_eY]
  have hnot : i ∉ oSet o x := by
    intro h
    obtain ⟨p, hp, hpo⟩ := Finset.mem_image.mp h
    exact hi p hpo
  rw [if_neg hnot]

private theorem eY_oSet_mul {o : Fin 8 → Fin 24} (ho : Function.Injective o)
    (x y : Multiplicative (Fin 6 → ZMod 2)) :
    eY (oSet o (x * y)) = eY (oSet o x) * eY (oSet o y) := by
  apply Multiplicative.toAdd.injective
  funext i
  by_cases hi : ∃ p, o p = i
  · obtain ⟨p, rfl⟩ := hi
    simp only [toAdd_eY_oSet_o ho (x * y) p, toAdd_mul, evVec_add, Pi.add_apply,
      toAdd_eY_oSet_o ho x p, toAdd_eY_oSet_o ho y p]
  · push Not at hi
    simp only [toAdd_eY_oSet_notMem (x * y) hi, toAdd_mul, Pi.add_apply,
      toAdd_eY_oSet_notMem x hi, toAdd_eY_oSet_notMem y hi, add_zero]

private theorem oSet_one {o : Fin 8 → Fin 24} :
    oSet o (1 : Multiplicative (Fin 6 → ZMod 2)) = ∅ := by
  unfold oSet
  ext i
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, hp, -⟩
    rw [show Multiplicative.toAdd (1 : Multiplicative (Fin 6 → ZMod 2)) = 0 from rfl] at hp
    simp [evVec] at hp
  · intro h
    exact absurd h (by simp)

private theorem eY_oSet_one {o : Fin 8 → Fin 24} :
    eY (oSet o (1 : Multiplicative (Fin 6 → ZMod 2))) = 1 := by
  rw [oSet_one, eY_empty]

private theorem eY_oSet_mem_coreMod {o : Fin 8 → Fin 24} (ho : Function.Injective o)
    (x : Multiplicative (Fin 6 → ZMod 2)) : eY (oSet o x) ∈ G6.coreMod 24 := by
  rw [G6.mem_coreMod]
  have hsub : (Finset.univ.sum fun i => Multiplicative.toAdd (eY (oSet o x)) i) =
      ((Finset.univ.image o).sum fun i => Multiplicative.toAdd (eY (oSet o x)) i) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    rw [toAdd_eY, if_neg (fun hmem => by
      obtain ⟨p, hp, hpo⟩ := Finset.mem_image.mp hmem
      exact hi (Finset.mem_image.mpr ⟨p, Finset.mem_univ p, hpo⟩))]
  rw [hsub, Finset.sum_image (fun p _ q _ h => ho h)]
  simp only [toAdd_eY_oSet_o ho x]
  exact evVec_even (Multiplicative.toAdd x)

private theorem eY_oSet_eq_of_ne {o : Fin 8 → Fin 24} (ho : Function.Injective o)
    (x : Multiplicative (Fin 6 → ZMod 2)) (T : Finset (Fin 24))
    (hT : ∀ i, i ∈ T ↔ ∃ p, o p = i ∧ evVec (Multiplicative.toAdd x) p ≠ 0) :
    eY (oSet o x) = eY T := by
  apply Multiplicative.toAdd.injective
  funext i
  by_cases hi : ∃ p, o p = i
  · obtain ⟨p, rfl⟩ := hi
    rw [toAdd_eY_oSet_o ho x p, toAdd_eY]
    by_cases hp : evVec (Multiplicative.toAdd x) p = 0
    · have hnotmem : o p ∉ T := fun hmem => by
        obtain ⟨q, hq, hqne⟩ := (hT (o p)).1 hmem
        have hqp : q = p := ho hq
        subst hqp
        exact hqne hp
      rw [if_neg hnotmem, hp]
    · have hmem : o p ∈ T := (hT (o p)).2 ⟨p, rfl, hp⟩
      rw [if_pos hmem]
      rcases h13_zmod2_cases (evVec (Multiplicative.toAdd x) p) with h0 | h1
      · exact absurd h0 hp
      · exact h1
  · push Not at hi
    rw [toAdd_eY_oSet_notMem x hi, toAdd_eY,
      if_neg (fun hmem => by
        obtain ⟨q, hq, _⟩ := (hT i).1 hmem
        exact hi q hq)]

private theorem eY_mul_eq (X Y : Finset (Fin 24)) : eY X * eY Y = eY (symmDiff X Y) := by
  apply Multiplicative.toAdd.injective
  funext i
  simp only [toAdd_mul, Pi.add_apply, toAdd_eY, Finset.mem_symmDiff]
  by_cases hx : i ∈ X <;> by_cases hy : i ∈ Y <;> simp [hx, hy] <;> decide

private theorem golayC_le_ker : golayC ≤ (mathModel false d a b Γ).ker := by
  show golayC ≤ (if d = 22 then golayC ⊔ Subgroup.zpowers (pairVec a b) else golayC)
  split_ifs with h
  · exact le_sup_left
  · exact le_rfl

theorem exists_phiData
    (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) : Nonempty (PhiData O β) := by
  obtain ⟨o, ho_inj, ho_mem, ho0, ho1⟩ :=
    exists_octad_enum hM.cfg.octad hM.cfg.a_O hM.cfg.b_O hM.cfg.ne
  let s : Multiplicative (Fin 6 → ZMod 2) →* ↥(mathModel false d a b Γ).sec :=
    { toFun := fun x => ⟨eY (oSet o x), eY_oSet_mem_coreMod ho_inj x⟩
      map_one' := by
        apply Subtype.ext
        exact eY_oSet_one
      map_mul' := fun x y => by
        apply Subtype.ext
        exact eY_oSet_mul ho_inj x y }
  obtain ⟨φ, hφ⟩ := exists_hom_vecOf hM s
  exact ⟨{ o := o
           o_inj := ho_inj
           o_mem := ho_mem
           o_zero := ho0
           o_one := ho1
           o_octad := hM.cfg.octad
           φ := φ
           vec := fun x => by simpa [s] using hφ x }⟩

namespace PhiData

variable (P : PhiData O β)

theorem equivariant (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) {g : ↥Γ} {σ : Equiv.Perm (Fin 8)}
    (hσ : ∀ p, (g : S24) (P.o p) = P.o (σ p)) (x : Multiplicative (Fin 6 → ZMod 2)) :
    ρ g (P.φ x) = P.φ (evActHom σ x) := by
  have htoAdd : Multiplicative.toAdd (evActHom σ x) = evAct σ (Multiplicative.toAdd x) := by
    simpa using evActHom_apply σ (Multiplicative.toAdd x)
  have hginv : ∀ q : Fin 8, (g : S24)⁻¹ (P.o q) = P.o (σ.symm q) := by
    intro q
    have h1 := hσ (σ.symm q)
    rw [Equiv.apply_symm_apply] at h1
    rw [← h1, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  have he_coord : ∀ q : Fin 8,
      Multiplicative.toAdd (eY ((oSet P.o x).map (g : S24).toEmbedding)) (P.o q) =
        evVec (Multiplicative.toAdd x) (σ.symm q) := by
    intro q
    rw [toAdd_eY_map (g : S24) (oSet P.o x) (P.o q), hginv q]
    exact toAdd_eY_oSet_o P.o_inj x (σ.symm q)
  have hf_coord : ∀ q : Fin 8,
      Multiplicative.toAdd (eY (oSet P.o (evActHom σ x))) (P.o q) =
        evVec (evAct σ (Multiplicative.toAdd x)) q := by
    intro q
    rw [toAdd_eY_oSet_o P.o_inj (evActHom σ x) q, htoAdd]
  have he_zero : ∀ i : Fin 24, (∀ q, P.o q ≠ i) →
      Multiplicative.toAdd (eY ((oSet P.o x).map (g : S24).toEmbedding)) i = 0 := by
    intro i hi
    rw [toAdd_eY_map (g : S24) (oSet P.o x) i]
    apply toAdd_eY_oSet_notMem x
    intro q hq
    exact hi (σ q) (by rw [← hσ q, hq, Equiv.Perm.inv_def, Equiv.apply_symm_apply])
  have hf_zero : ∀ i : Fin 24, (∀ q, P.o q ≠ i) →
      Multiplicative.toAdd (eY (oSet P.o (evActHom σ x))) i = 0 :=
    fun i hi => toAdd_eY_oSet_notMem (evActHom σ x) hi
  have hef : eY ((oSet P.o x).map (g : S24).toEmbedding) *
      (eY (oSet P.o (evActHom σ x)))⁻¹ ∈ (mathModel false d a b Γ).ker := by
    rcases evVec_evAct σ (Multiplicative.toAdd x) with hcase | hcase
    · have hzero : ∀ i, Multiplicative.toAdd
          (eY ((oSet P.o x).map (g : S24).toEmbedding) *
            (eY (oSet P.o (evActHom σ x)))⁻¹) i = 0 := by
        intro i
        by_cases hi : ∃ q, P.o q = i
        · obtain ⟨q, rfl⟩ := hi
          rw [toAdd_mul, Pi.add_apply, inv24_eq, he_coord q]
          have hfq : Multiplicative.toAdd (eY (oSet P.o (evActHom σ x))) (P.o q) =
              evVec (Multiplicative.toAdd x) (σ.symm q) := by
            simpa [hf_coord q, hcase]
          rw [hfq]
          exact CharTwo.add_self_eq_zero _
        · push Not at hi
          simp only [toAdd_mul, Pi.add_apply, inv24_eq, he_zero i hi, hf_zero i hi, zero_add]
      have hone : eY ((oSet P.o x).map (g : S24).toEmbedding) *
          (eY (oSet P.o (evActHom σ x)))⁻¹ = 1 := by
        apply Multiplicative.toAdd.injective
        funext i
        simpa using hzero i
      rw [hone]
      change (1 : (mathModel false d a b Γ).Amb) ∈ (mathModel false d a b Γ).ker
      exact Subgroup.one_mem _
    · have hE : eY ((oSet P.o x).map (g : S24).toEmbedding) *
          (eY (oSet P.o (evActHom σ x)))⁻¹ = eY O := by
        apply Multiplicative.toAdd.injective
        funext i
        rw [toAdd_mul, Pi.add_apply, inv24_eq]
        by_cases hi : ∃ q, P.o q = i
        · obtain ⟨q, rfl⟩ := hi
          have hfq : Multiplicative.toAdd (eY (oSet P.o (evActHom σ x))) (P.o q) =
              evVec (Multiplicative.toAdd x) (σ.symm q) + 1 := by
            simpa [hf_coord q, hcase]
          rw [he_coord q, hfq, toAdd_eY, if_pos ((P.o_mem (P.o q)).2 ⟨q, rfl⟩),
            ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
        · push Not at hi
          simp only [he_zero i hi, hf_zero i hi, zero_add, toAdd_eY,
            if_neg (fun hmem => by
              obtain ⟨q, hq⟩ := (P.o_mem i).1 hmem
              exact hi q hq)]
      rw [hE]
      change (eY O : (mathModel false d a b Γ).Amb) ∈ (mathModel false d a b Γ).ker
      exact golayC_le_ker P.o_octad.2
  have hv : IsVecOf (mathModel false d a b Γ) β
      (G6.permAct 24 (g : S24) (eY (oSet P.o x))) (ρ g (P.φ x)) :=
    isVecOf_act hM (P.vec x) g
  rw [permAct_eY] at hv
  have hfmem : eY (oSet P.o (evActHom σ x)) ∈ (mathModel false d a b Γ).sec :=
    eY_oSet_mem_coreMod P.o_inj (evActHom σ x)
  have hv' : IsVecOf (mathModel false d a b Γ) β
      (eY (oSet P.o (evActHom σ x))) (ρ g (P.φ x)) :=
    isVecOf_congr hM hv hfmem hef
  exact isVecOf_unique hM hv' (P.vec (evActHom σ x))

theorem isVecOf_pair (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) {p q : Fin 8} (hpq : p ≠ q) :
    IsVecOf (mathModel false d a b Γ) β (pairVec (P.o p) (P.o q))
      (P.φ (Multiplicative.ofAdd (evPair p q))) := by
  have hne : P.o p ≠ P.o q := fun h => hpq (P.o_inj h)
  have hchar : ∀ t : Fin 8,
      ((if t = p ∨ t = q then (1 : ZMod 2) else 0) + 1 ≠ 0 ↔ t ≠ p ∧ t ≠ q) := by
    intro t
    by_cases ht2 : t = p ∨ t = q
    · rw [if_pos ht2]
      constructor
      · intro h
        exact absurd (by decide : (1 : ZMod 2) + 1 = 0) h
      · rintro ⟨hp, hq⟩
        rcases ht2 with h | h
        · exact absurd h hp
        · exact absurd h hq
    · rw [if_neg ht2]
      constructor
      · intro _
        exact not_or.mp ht2
      · intro _
        decide
  have hf : pairVec (P.o p) (P.o q) ∈ (mathModel false d a b Γ).sec :=
    pairVec_mem_coreMod_of_ne (P.o p) (P.o q) hne
  have hef : eY (oSet P.o (Multiplicative.ofAdd (evPair p q))) *
      (pairVec (P.o p) (P.o q))⁻¹ ∈ (mathModel false d a b Γ).ker := by
    rcases evVec_evPair hpq with hcase | hcase
    · have hT : ∀ i, i ∈ ({P.o p, P.o q} : Finset (Fin 24)) ↔
          ∃ t, P.o t = i ∧ evVec (evPair p q) t ≠ 0 := by
        intro i
        rw [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro (rfl | rfl)
          · exact ⟨p, rfl, by rw [hcase]; simp [hpq]⟩
          · exact ⟨q, rfl, by rw [hcase]; simp [Ne.symm hpq]⟩
        · rintro ⟨t, ht, htne⟩
          have htne' : (if t = p ∨ t = q then (1 : ZMod 2) else 0) ≠ 0 := by
            have := htne
            rw [hcase] at this
            simpa using this
          by_cases ht2 : t = p ∨ t = q
          · rcases ht2 with rfl | rfl
            · exact Or.inl ht.symm
            · exact Or.inr ht.symm
          · exfalso
            have h0 : (if t = p ∨ t = q then (1 : ZMod 2) else 0) = 0 := by simp [ht2]
            exact htne' h0
      have he : (eY (oSet P.o (Multiplicative.ofAdd (evPair p q))) : PM24) =
          (pairVec (P.o p) (P.o q) : PM24) := by
        rw [eY_oSet_eq_of_ne P.o_inj (Multiplicative.ofAdd (evPair p q))
          ({P.o p, P.o q} : Finset (Fin 24)) hT, pairVec_eq_eY_pair (P.o p) (P.o q) hne]
      have hone : (eY (oSet P.o (Multiplicative.ofAdd (evPair p q))) *
          (pairVec (P.o p) (P.o q))⁻¹ : PM24) = 1 := by
        rw [he, inv24_eq, sq24]
      rw [hone]
      change (1 : (mathModel false d a b Γ).Amb) ∈ (mathModel false d a b Γ).ker
      exact Subgroup.one_mem _
    · have hT : ∀ i, i ∈ O \ ({P.o p, P.o q} : Finset (Fin 24)) ↔
          ∃ t, P.o t = i ∧ evVec (evPair p q) t ≠ 0 := by
        intro i
        rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hiO, hine⟩
          obtain ⟨t, ht⟩ := (P.o_mem i).1 hiO
          refine ⟨t, ht, ?_⟩
          have htne' : (if t = p ∨ t = q then (1 : ZMod 2) else 0) + 1 ≠ 0 := by
            rw [hchar t]
            exact ⟨fun htp => (not_or.mp hine).1 (by rw [← ht, htp]),
              fun htq => (not_or.mp hine).2 (by rw [← ht, htq])⟩
          rw [hcase]
          simpa using htne'
        · rintro ⟨t, ht, htne⟩
          refine ⟨(P.o_mem i).2 ⟨t, ht⟩, ?_⟩
          have htne' : (if t = p ∨ t = q then (1 : ZMod 2) else 0) + 1 ≠ 0 := by
            have := htne
            rw [hcase] at this
            simpa using this
          have hnk := (hchar t).1 htne'
          rintro (h | h)
          · exact hnk.1 (P.o_inj (ht.trans h))
          · exact hnk.2 (P.o_inj (ht.trans h))
      have hTsd : O \ ({P.o p, P.o q} : Finset (Fin 24)) =
          O ∆ ({P.o p, P.o q} : Finset (Fin 24)) := by
        have hsub : ({P.o p, P.o q} : Finset (Fin 24)) ⊆ O := by
          intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · exact (P.o_mem _).2 ⟨p, rfl⟩
          · rw [Finset.mem_singleton] at hj
            subst hj
            exact (P.o_mem _).2 ⟨q, rfl⟩
        ext i
        rw [Finset.mem_sdiff, Finset.mem_symmDiff]
        constructor
        · rintro ⟨hiO, hip⟩
          exact Or.inl ⟨hiO, hip⟩
        · rintro (⟨hiO, hip⟩ | ⟨hip, hiO⟩)
          · exact ⟨hiO, hip⟩
          · exact absurd (hsub hip) hiO
      have he : (eY (oSet P.o (Multiplicative.ofAdd (evPair p q))) : PM24) =
          (eY O * pairVec (P.o p) (P.o q) : PM24) := by
        rw [eY_oSet_eq_of_ne P.o_inj (Multiplicative.ofAdd (evPair p q))
          (O \ ({P.o p, P.o q} : Finset (Fin 24))) hT, hTsd, ← eY_mul_eq,
          pairVec_eq_eY_pair (P.o p) (P.o q) hne]
      have hcone : ((eY O * pairVec (P.o p) (P.o q)) *
          (pairVec (P.o p) (P.o q))⁻¹ : PM24) = eY O := by
        rw [inv24_eq, mul_assoc, sq24, mul_one]
      have hprod : (eY (oSet P.o (Multiplicative.ofAdd (evPair p q))) *
          (pairVec (P.o p) (P.o q))⁻¹ : PM24) = eY O := by rw [he, hcone]
      rw [hprod]
      change (eY O : (mathModel false d a b Γ).Amb) ∈ (mathModel false d a b Γ).ker
      exact golayC_le_ker P.o_octad.2
  exact isVecOf_congr hM (P.vec (Multiplicative.ofAdd (evPair p q))) hf hef

theorem isO2Vec (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) {p q : Fin 8} (hpq : p ≠ q)
    (h : d = 24 ∨ (d = 23 ∧ p = 0) ∨ (d = 22 ∧ p = 0 ∧ 2 ≤ q.val)) :
    IsO2Vec d a b Γ β (P.φ (Multiplicative.ofAdd (evPair p q))) := by
  refine ⟨P.o p, P.o q, fun hh => hpq (P.o_inj hh), ?_, P.isVecOf_pair hM hpq⟩
  rcases h with h24 | ⟨h23, hp⟩ | ⟨h22, hp, hq2⟩
  · exact Or.inl h24
  · exact Or.inr (Or.inl ⟨h23, by rw [hp, P.o_zero]⟩)
  · refine Or.inr (Or.inr ⟨h22, Or.inl (by rw [hp, P.o_zero]), ?_, ?_⟩)
    · intro hq0
      have hq : q = 0 := P.o_inj (by rw [hq0, P.o_zero])
      rw [hq] at hq2
      simp at hq2
    · intro hq1
      have hq : q = 1 := P.o_inj (by rw [hq1, P.o_one])
      rw [hq] at hq2
      simp at hq2

end PhiData

end CFSG.ASVolI.AppH

