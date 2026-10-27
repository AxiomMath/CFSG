module

public import CFSG.LocalAnalysis.StandardType.TableC.POmegaBlockElement
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockOmegaIsoOneLinear
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockOmegaIsoUnitary

public section

namespace CFSG.StandardType.TableC

open Module QuadraticMap
open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal CFSG.RankThree.Classical2
open CFSG.StandardType.ClassicalPosition
open CFSG.StandardType.ClassicalBlocks

private lemma j1c_pairwise_commute {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {S : Set (GL ι K)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') :
    (Units.val '' S : Set (Matrix ι ι K)).Pairwise Commute := by
  rintro a ⟨s, hs, rfl⟩ b ⟨s', hs', rfl⟩ _
  show (s : Matrix ι ι K) * (s' : Matrix ι ι K) =
    (s' : Matrix ι ι K) * (s : Matrix ι ι K)
  rw [← Units.val_mul, ← Units.val_mul]
  exact congrArg Units.val (hS s hs s' hs').eq

private lemma j1c_prim_orthogonal {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {S : Set (GL ι K)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e e' : Matrix ι ι K}
    (he : IsPrimIdemIn (Algebra.adjoin K (Units.val '' S)) e)
    (he' : IsPrimIdemIn (Algebra.adjoin K (Units.val '' S)) e')
    (hne : e ≠ e') (hεe : ε = e + e') :
    e * e' = 0 ∧ e * ε = e ∧ e' * ε = e' := by
  let A : Subalgebra K (Matrix ι ι K) := Algebra.adjoin K (Units.val '' S)
  letI : CommRing A := Algebra.adjoinCommRingOfComm K (j1c_pairwise_commute hS)
  have heA : IsIdempotentElem (⟨e, he.1⟩ : A) := by
    rw [isIdempotentElem_iff]
    exact Subtype.ext he.2.1.eq
  have heA' : IsIdempotentElem (⟨e', he'.1⟩ : A) := by
    rw [isIdempotentElem_iff]
    exact Subtype.ext he'.2.1.eq
  have hp_idem : IsIdempotentElem (e * e') := by
    rw [isIdempotentElem_iff]
    have h := IsIdempotentElem.mul heA heA'
    rw [isIdempotentElem_iff] at h
    simpa only [Subalgebra.coe_mul] using congrArg Subtype.val h
  have hcomm_ee' : e' * e = e * e' := by
    have h := mul_comm (⟨e', he'.1⟩ : A) (⟨e, he.1⟩ : A)
    simpa only [Subalgebra.coe_mul] using congrArg Subtype.val h
  have hpe : (e * e') * e = e * e' := by
    rw [Matrix.mul_assoc, hcomm_ee', ← Matrix.mul_assoc, he.2.1.eq]
  have hpA : e * e' ∈ A := A.mul_mem he.1 he'.1
  have hee' : e * e' = 0 := by
    rcases he.2.2.2 (e * e') hpA hp_idem hpe with h0 | heq
    · exact h0
    · exfalso
      rcases he'.2.2.2 e he.1 he.2.1 heq with h0 | heq2
      · exact he.2.2.1 h0
      · exact hne heq2
  refine ⟨hee', ?_, ?_⟩
  · rw [hεe, Matrix.mul_add, he.2.1.eq, hee', add_zero]
  · rw [hεe, Matrix.mul_add, (by rw [hcomm_ee', hee'] : e' * e = 0), he'.2.1.eq,
      zero_add]

private lemma j1c_fixed_prim_idem_eq {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {S : Set (GL ι K)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e e' : Matrix ι ι K}
    (he : IsPrimIdemIn (Algebra.adjoin K (Units.val '' S)) e)
    (he' : IsPrimIdemIn (Algebra.adjoin K (Units.val '' S)) e')
    (hfix : ∀ s ∈ S, (s : Matrix ι ι K) * e = e ∧ (s : Matrix ι ι K) * e' = e') :
    e = e' := by
  let A : Subalgebra K (Matrix ι ι K) := Algebra.adjoin K (Units.val '' S)
  letI : CommRing A := Algebra.adjoinCommRingOfComm K (j1c_pairwise_commute hS)
  have hP : ∀ x ∈ A, ∃ c : K, x * e = c • e ∧ x * e' = c • e' := by
    intro x hx
    refine Algebra.adjoin_induction
      (p := fun x _ => ∃ c : K, x * e = c • e ∧ x * e' = c • e') ?_ ?_ ?_ ?_ hx
    · rintro y ⟨s, hs, rfl⟩
      exact ⟨1, by rw [one_smul, (hfix s hs).1], by rw [one_smul, (hfix s hs).2]⟩
    · intro r
      exact ⟨r, by rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul],
        by rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul]⟩
    · intro y z _ _ ⟨c, hc1, hc2⟩ ⟨d, hd1, hd2⟩
      exact ⟨c + d, by rw [Matrix.add_mul, hc1, hd1, add_smul],
        by rw [Matrix.add_mul, hc2, hd2, add_smul]⟩
    · intro y z _ _ ⟨c, hc1, hc2⟩ ⟨d, hd1, hd2⟩
      refine ⟨d * c, ?_, ?_⟩
      · rw [Matrix.mul_assoc, hd1, Matrix.mul_smul, hc1, smul_smul]
      · rw [Matrix.mul_assoc, hd2, Matrix.mul_smul, hc2, smul_smul]
  obtain ⟨c, hce, hce'⟩ := hP e he.1
  have hc : c = 1 := by
    apply smul_left_injective K he.2.2.1
    change c • e = 1 • e
    rw [← hce, he.2.1.eq, one_smul]
  have he_eq : e * e' = e' := by rw [hce', hc, one_smul]
  have hcomm_ee' : e' * e = e * e' := by
    have h := mul_comm (⟨e', he'.1⟩ : A) (⟨e, he.1⟩ : A)
    simpa only [Subalgebra.coe_mul] using congrArg Subtype.val h
  rcases he.2.2.2 e' he'.1 he'.2.1 (by rw [hcomm_ee', he_eq]) with h0 | h
  · exact absurd h0 he'.2.2.1
  · exact h.symm

private lemma j1c_nontrivial_of_dual {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {S : Set (GL ι K)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e e' : Matrix ι ι K}
    (he : IsPrimIdemIn (Algebra.adjoin K (Units.val '' S)) e)
    (he' : IsPrimIdemIn (Algebra.adjoin K (Units.val '' S)) e')
    (hne : e ≠ e') (hεe : ε = e + e') :
    ∃ s ∈ S, (s : Matrix ι ι K) * ε ≠ ε := by
  by_contra h
  push Not at h
  have hcommP := j1c_pairwise_commute hS
  let A : Subalgebra K (Matrix ι ι K) := Algebra.adjoin K (Units.val '' S)
  letI : CommRing A := Algebra.adjoinCommRingOfComm K hcommP
  obtain ⟨hee', heε, he'ε⟩ := j1c_prim_orthogonal hS he he' hne hεe
  have hzero' : e' * e = 0 := by
    have h := mul_comm (⟨e', he'.1⟩ : A) (⟨e, he.1⟩ : A)
    have h' : e' * e = e * e' := by
      simpa only [Subalgebra.coe_mul] using congrArg Subtype.val h
    rw [h', hee']
  have hfix : ∀ s ∈ S, (s : Matrix ι ι K) * e = e ∧ (s : Matrix ι ι K) * e' = e' := by
    intro s hs
    have hsA : (s : Matrix ι ι K) ∈ A := Algebra.subset_adjoin ⟨s, hs, rfl⟩
    have hcomm_es : e * (s : Matrix ι ι K) = (s : Matrix ι ι K) * e := by
      have h := mul_comm (⟨e, he.1⟩ : A) (⟨(s : Matrix ι ι K), hsA⟩ : A)
      simpa only [Subalgebra.coe_mul] using congrArg Subtype.val h
    have hcomm_e's : e' * (s : Matrix ι ι K) = (s : Matrix ι ι K) * e' := by
      have h := mul_comm (⟨e', he'.1⟩ : A) (⟨(s : Matrix ι ι K), hsA⟩ : A)
      simpa only [Subalgebra.coe_mul] using congrArg Subtype.val h
    have h1 : e * ((s : Matrix ι ι K) * ε) = e := by rw [h s hs, heε]
    have h2 : e * ((s : Matrix ι ι K) * ε) = (s : Matrix ι ι K) * e := by
      calc e * ((s : Matrix ι ι K) * ε)
          = e * ((s : Matrix ι ι K) * (e + e')) := by rw [hεe]
        _ = e * ((s : Matrix ι ι K) * e + (s : Matrix ι ι K) * e') := by
              rw [Matrix.mul_add]
        _ = e * ((s : Matrix ι ι K) * e) + e * ((s : Matrix ι ι K) * e') := by
              rw [Matrix.mul_add]
        _ = (e * (s : Matrix ι ι K)) * e + (e * (s : Matrix ι ι K)) * e' := by
              rw [← Matrix.mul_assoc e (s : Matrix ι ι K) e,
                ← Matrix.mul_assoc e (s : Matrix ι ι K) e']
        _ = ((s : Matrix ι ι K) * e) * e + ((s : Matrix ι ι K) * e) * e' := by
              rw [hcomm_es]
        _ = (s : Matrix ι ι K) * (e * e) + (s : Matrix ι ι K) * (e * e') := by
              rw [Matrix.mul_assoc, Matrix.mul_assoc]
        _ = (s : Matrix ι ι K) * e + (s : Matrix ι ι K) * 0 := by
              rw [he.2.1.eq, hee']
        _ = (s : Matrix ι ι K) * e := by rw [Matrix.mul_zero, add_zero]
    have h1' : e' * ((s : Matrix ι ι K) * ε) = e' := by rw [h s hs, he'ε]
    have h2' : e' * ((s : Matrix ι ι K) * ε) = (s : Matrix ι ι K) * e' := by
      calc e' * ((s : Matrix ι ι K) * ε)
          = e' * ((s : Matrix ι ι K) * (e + e')) := by rw [hεe]
        _ = e' * ((s : Matrix ι ι K) * e + (s : Matrix ι ι K) * e') := by
              rw [Matrix.mul_add]
        _ = e' * ((s : Matrix ι ι K) * e) + e' * ((s : Matrix ι ι K) * e') := by
              rw [Matrix.mul_add]
        _ = (e' * (s : Matrix ι ι K)) * e + (e' * (s : Matrix ι ι K)) * e' := by
              rw [← Matrix.mul_assoc e' (s : Matrix ι ι K) e,
                ← Matrix.mul_assoc e' (s : Matrix ι ι K) e']
        _ = ((s : Matrix ι ι K) * e') * e + ((s : Matrix ι ι K) * e') * e' := by
              rw [hcomm_e's]
        _ = (s : Matrix ι ι K) * (e' * e) + (s : Matrix ι ι K) * (e' * e') := by
              rw [Matrix.mul_assoc, Matrix.mul_assoc]
        _ = (s : Matrix ι ι K) * 0 + (s : Matrix ι ι K) * e' := by
              rw [hzero', he'.2.1.eq]
        _ = (s : Matrix ι ι K) * e' := by rw [Matrix.mul_zero, zero_add]
    exact ⟨by rw [← h2, h1], by rw [← h2', h1']⟩
  exact hne (j1c_fixed_prim_idem_eq hS he he' hfix)

private noncomputable def j1c_block_equiv {ι K U : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Group U] (Φ : QuadraticForm K (ι → K))
    (j : U →* GL ι K) (hj : Function.Injective j) (hrange : j.range = StatedOmega ⇑Φ)
    {S S' : Set (GL ι K)} {ε : Matrix ι ι K}
    (hmem : ∀ g ∈ StatedOmega ⇑Φ,
      (g ∈ Subgroup.centralizer S ∧ g ∈ glFixing (1 - ε)) ↔
      (g ∈ Subgroup.centralizer S' ∧ g ∈ glFixing (1 - ε))) :
    ↥(glBlockCentralizer j S ε) ≃*
      ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype S' ε) := by
  let f : U →* StatedOmega ⇑Φ :=
    { toFun := fun u => ⟨j u, hrange.le (show j u ∈ j.range from ⟨u, rfl⟩)⟩
      map_one' := Subtype.ext j.map_one
      map_mul' := fun a b => Subtype.ext (j.map_mul a b) }
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      exact hj (congrArg Subtype.val hab)
    · intro h
      obtain ⟨u, hu⟩ := hrange.symm.le h.2
      exact ⟨u, Subtype.ext hu⟩
  let e0 : U ≃* StatedOmega ⇑Φ := MulEquiv.ofBijective f hf
  have hEq : (glBlockCentralizer j S ε).map e0.toMonoidHom =
      glBlockCentralizer (StatedOmega ⇑Φ).subtype S' ε := by
    ext g
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hju : j u ∈ StatedOmega ⇑Φ := hrange.le (show j u ∈ j.range from ⟨u, rfl⟩)
      have hu' : j u ∈ Subgroup.centralizer S ∧ j u ∈ glFixing (1 - ε) := by
        simp only [glBlockCentralizer, Subgroup.mem_comap, Subgroup.mem_inf] at hu
        exact hu
      rw [glBlockCentralizer, Subgroup.mem_comap, Subgroup.mem_inf]
      exact (hmem (j u) hju).mp hu'
    · intro hg
      have hgu : (g : GL ι K) ∈ Subgroup.centralizer S' ∧
          (g : GL ι K) ∈ glFixing (1 - ε) := by
        simp only [glBlockCentralizer, Subgroup.mem_comap, Subgroup.mem_inf] at hg
        exact hg
      obtain ⟨u, hu⟩ := hrange.symm.le g.2
      refine ⟨u, ?_, Subtype.ext hu⟩
      have hju : j u ∈ StatedOmega ⇑Φ := hrange.le (show j u ∈ j.range from ⟨u, rfl⟩)
      have hmem' : j u ∈ Subgroup.centralizer S ∧ j u ∈ glFixing (1 - ε) := by
        rw [← hu] at hgu
        exact (hmem (j u) hju).mpr hgu
      rw [glBlockCentralizer, Subgroup.mem_comap, Subgroup.mem_inf]
      exact hmem'
  exact (Subgroup.equivMapOfInjective _ e0.toMonoidHom e0.injective).trans
    (MulEquiv.subgroupCongr hEq)

theorem blockGroup_iso_Omega_linear_S {ι K U : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] [Group U] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (j : U →* GL ι K) (hj : Function.Injective j) (hrange : j.range = StatedOmega ⇑Φ)
    (S : Set (GL ι K)) (hSU : ∀ s ∈ S, s ∈ j.range) (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s)) {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' S)) ε)
    {e e' : Matrix ι ι K} (he : IsPrimIdemIn (Algebra.adjoin K (Units.val '' S)) e)
    (he' : IsPrimIdemIn (Algebra.adjoin K (Units.val '' S)) e') (hne : e ≠ e')
    (hεe : ε = e + e') :
    ∃ (d m : ℕ) (E : Type) (_ : Field E) (_ : Fintype E), 1 ≤ d ∧
      Fintype.card E = Fintype.card K ^ d ∧
      2 * d * m = Module.finrank K (LinearMap.range (Matrix.toLin' ε)) ∧
      blockDegree (Algebra.adjoin K (Units.val '' S)) e = d ∧
      Nonempty (↥(glBlockCentralizer j S ε) ≃* GL (Fin m) E) := by
  have hSΩ : ∀ s ∈ S, s ∈ StatedOmega ⇑Φ := fun s hs => hrange.le (hSU s hs)
  have hnt : ∃ s ∈ S, (s : Matrix ι ι K) * ε ≠ ε :=
    j1c_nontrivial_of_dual hS he he' hne hεe
  obtain ⟨b, hb, hbodd, hbε, _hbne, hcent, hblockdeg⟩ :=
    exists_blockElement_nontrivial Φ hΦ h8 S hSΩ hS hodd hε hnt
  obtain ⟨_, heε, he'ε⟩ := j1c_prim_orthogonal hS he he' hne hεe
  obtain ⟨heb, hdeg_b⟩ := hblockdeg e he heε
  obtain ⟨heb', _⟩ := hblockdeg e' he' he'ε
  obtain ⟨d, m, E, hE, hEfin, hd1, hcard, hdim, hdegW, ⟨eGL⟩⟩ :=
    blockGroup_iso_Omega_linear Φ hΦ h8 b hb hbodd hbε heb heb' hne hεe
  refine ⟨d, m, E, hE, hEfin, hd1, hcard, hdim, ?_, ?_⟩
  · rw [← hdeg_b, hdegW]
  · exact ⟨(j1c_block_equiv Φ j hj hrange hcent).trans eGL⟩

theorem blockGroup_iso_Omega_unitary_S {ι K U : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] [Group U] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (j : U →* GL ι K) (hj : Function.Injective j) (hrange : j.range = StatedOmega ⇑Φ)
    (S : Set (GL ι K)) (hSU : ∀ s ∈ S, s ∈ j.range) (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s)) {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' S)) ε)
    (hp : IsPrimIdemIn (Algebra.adjoin K (Units.val '' S)) ε)
    (h1 : ∃ s ∈ S, (s : Matrix ι ι K) * ε ≠ ε) :
    ∃ (d m : ℕ) (E : Type) (_ : Field E) (_ : Fintype E), 1 ≤ d ∧
      Fintype.card E = (Fintype.card K ^ d) ^ 2 ∧
      2 * d * m = Module.finrank K (LinearMap.range (Matrix.toLin' ε)) ∧
      blockDegree (Algebra.adjoin K (Units.val '' S)) ε = 2 * d ∧
      Nonempty (↥(glBlockCentralizer j S ε) ≃* ↥(GUFull m (Fintype.card K ^ d) E)) := by
  have hSΩ : ∀ s ∈ S, s ∈ StatedOmega ⇑Φ := fun s hs => hrange.le (hSU s hs)
  obtain ⟨b, hb, hbodd, hbε, hbne, hcent, hblockdeg⟩ :=
    exists_blockElement_nontrivial Φ hΦ h8 S hSΩ hS hodd hε h1
  obtain ⟨hp_b, hdeg_b⟩ := hblockdeg ε hp hε.2.1.eq
  obtain ⟨d, m, E, hE, hEfin, hd1, hcard, hdim, hdegW, ⟨eGU⟩⟩ :=
    blockGroup_iso_Omega_unitary Φ hΦ h8 b hb hbodd hbε hp_b hbne
  refine ⟨d, m, E, hE, hEfin, hd1, hcard, hdim, ?_, ?_⟩
  · rw [← hdeg_b, hdegW]
  · exact ⟨(j1c_block_equiv Φ j hj hrange hcent).trans eGU⟩

theorem blockGroup_iso_Omega_one_S {ι K U : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] [Group U] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (j : U →* GL ι K) (hj : Function.Injective j) (hrange : j.range = StatedOmega ⇑Φ)
    (S : Set (GL ι K)) (hSU : ∀ s ∈ S, s ∈ j.range) (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s)) {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' S)) ε)
    (h1 : ∀ s ∈ S, (s : Matrix ι ι K) * ε = ε) :
    ∃ (ι₁ : Type) (_ : Fintype ι₁) (_ : DecidableEq ι₁) (Q₁ : (ι₁ → K) → K),
      Fintype.card ι₁ = Module.finrank K (LinearMap.range (Matrix.toLin' ε)) ∧
      (∃ Φ₁ : QuadraticForm K (ι₁ → K), ⇑Φ₁ = Q₁ ∧ (QuadraticMap.polarBilin Φ₁).Nondegenerate) ∧
      ((Nonempty (↥(glBlockCentralizer j S ε) ≃* ↥(StatedOmega Q₁)) ∧
          ¬ (Fintype.card K = 2 ∧ Fintype.card ι₁ = 4 ∧
              ∃ T : Submodule K (ι₁ → K), Module.finrank K T = 2 ∧ ∀ x ∈ T, Q₁ x = 0)) ∨
        (Fintype.card K = 2 ∧ Fintype.card ι₁ = 4 ∧ IsSolvable ↥(glBlockCentralizer j S ε) ∧
          padicValNat 2 (Nat.card ↥(glBlockCentralizer j S ε)) = 2)) := by
  have hSΩ : ∀ s ∈ S, s ∈ StatedOmega ⇑Φ := fun s hs => hrange.le (hSU s hs)
  obtain ⟨b, hb, hbodd, hbε, hb1, hcent⟩ :=
    exists_blockElement_trivial Φ hΦ h8 S hSΩ hS hodd hε h1
  obtain ⟨ι₁, hι₁fin, hι₁dec, Q₁, hcard, hΦ₁part, hdisj⟩ :=
    blockGroup_iso_Omega_one Φ hΦ h8 b hb hbodd hbε hb1
  refine ⟨ι₁, hι₁fin, hι₁dec, Q₁, hcard, hΦ₁part, ?_⟩
  rcases hdisj with ⟨hiso, hnot⟩ | ⟨hK2, hι14, hsol, hpad⟩
  · obtain ⟨hiso⟩ := hiso
    left
    exact ⟨⟨(j1c_block_equiv Φ j hj hrange hcent).trans hiso⟩, hnot⟩
  · right
    refine ⟨hK2, hι14, ?_, ?_⟩
    · haveI : Group.IsSolvable ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) := hsol
      exact solvable_of_surjective
        (f := (j1c_block_equiv Φ j hj hrange hcent).symm.toMonoidHom)
        (j1c_block_equiv Φ j hj hrange hcent).symm.surjective
    · rw [Nat.card_congr (j1c_block_equiv Φ j hj hrange hcent).toEquiv]
      exact hpad

end CFSG.StandardType.TableC

end
