module

public import CFSG.LocalAnalysis.StandardType.GGTBTorRelDMinusDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalBasic
public import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega
public import CFSG.RankThree.PartTwo.Sec21.Hering2125Mat

public section

namespace CFSG.StandardType

namespace RelDMinus

open CFSG.Assembly Matrix TableBSymp CFSG.LieType.Universal.Spin

open scoped commutatorElement

variable {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ} {b c : K}

theorem torusGL_mem_omega (x : Fin m → Kˣ) :
    torusGL K m x ∈ LargeEvenOmega (LargeEvenQMinus m b c) := by
  rw [torusGL_apply]
  refine blockInl_mem_omegaMinus b c ?_
  choose y hy using fun i : Fin m =>
    CFSG.RankThree.PartTwo.Sec21.Hering2125.exists_sq_eq (x i)
  have hy' : y * y = x := by
    funext i
    exact hy i
  set w := TauCeti.permutationGL (k := K) (Equiv.sumComm (Fin m) (Fin m)) with hw
  have hmem : ⁅TauCeti.diagGL (pairedUnits y), w⁆ ∈ LargeEvenOmega (LargeEvenQPlus K m) :=
    Subgroup.commutator_mem_commutator (diagGL_pairedUnits_mem_orthPlus y) sumComm_mem_orthPlus
  have hconj : w * TauCeti.diagGL (pairedUnits y) * w⁻¹ =
      (TauCeti.diagGL (pairedUnits y))⁻¹ := permutationGL_sumComm_conj y
  have hpair : pairedUnits y * pairedUnits y = pairedUnits x := by
    rw [← pairedHom_apply, ← pairedHom_apply, ← map_mul, hy', pairedHom_apply]
  have hsquare : TauCeti.diagGL (pairedUnits y) * TauCeti.diagGL (pairedUnits y) =
      TauCeti.diagGL (pairedUnits x) := by
    rw [← map_mul, hpair]
  have hcomm : ⁅TauCeti.diagGL (pairedUnits y), w⁆ = TauCeti.diagGL (pairedUnits x) := by
    rw [commutatorElement_def]
    calc TauCeti.diagGL (pairedUnits y) * w * (TauCeti.diagGL (pairedUnits y))⁻¹ * w⁻¹
        = TauCeti.diagGL (pairedUnits y) *
            (w * TauCeti.diagGL (pairedUnits y) * w⁻¹)⁻¹ := by group
      _ = TauCeti.diagGL (pairedUnits y) * TauCeti.diagGL (pairedUnits y) := by
            rw [hconj, inv_inv]
      _ = TauCeti.diagGL (pairedUnits x) := hsquare
  rwa [hcomm] at hmem

theorem torusGL_injective : Function.Injective (torusGL K m) := by
  intro x y hxy
  have h1 : TauCeti.diagGL (pairedUnits x) = TauCeti.diagGL (pairedUnits y) := by
    apply Units.ext
    ext i j
    have h := congrArg (fun g : GL (LargeEvenMinusIdx m) K =>
      (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) (Sum.inl i) (Sum.inl j)) hxy
    simpa [torusGL_apply, coe_blockInl, Matrix.diagonal_apply] using h
  have h2 : pairedUnits x = pairedUnits y := TauCeti.diagGL_injective h1
  funext i
  have := congrFun h2 (Sum.inl i)
  simpa [pairedUnits] using this

@[expose] noncomputable def torus :
    (Fin m → Kˣ) →* ↥(LargeEvenOmega (LargeEvenQMinus m b c)) :=
  (torusGL K m).codRestrict _ fun x =>
    torusGL_mem_omega (K := K) (m := m) (b := b) (c := c) x

theorem coe_torus (x : Fin m → Kˣ) :
    (torus (K := K) (m := m) (b := b) (c := c) x : GL (LargeEvenMinusIdx m) K) =
      torusGL K m x :=
  rfl

theorem torus_injective :
    Function.Injective (torus (K := K) (m := m) (b := b) (c := c)) :=
  fun x y h => torusGL_injective (Subtype.ext_iff.mp h)

@[expose] noncomputable def swapGL (k : Fin m) (hk : k.val + 1 < m) :
    GL (LargeEvenMinusIdx m) K :=
  blockInl (TauCeti.permutationGL (k := K)
    (Equiv.Perm.sumCongr (Equiv.swap k ⟨k.val + 1, hk⟩) (Equiv.swap k ⟨k.val + 1, hk⟩)))

theorem permutationGL_pairPerm_mem_omegaPlus (k : Fin m) (hk : k.val + 1 < m) (hm : 3 ≤ m) :
    TauCeti.permutationGL (k := K)
        (Equiv.Perm.sumCongr (Equiv.swap k ⟨k.val + 1, hk⟩)
          (Equiv.swap k ⟨k.val + 1, hk⟩)) ∈
      LargeEvenOmega (LargeEvenQPlus K m) := by
  set l : Fin m := ⟨k.val + 1, hk⟩ with hl
  have hkl : k ≠ l := by
    intro h
    rw [hl] at h
    exact Nat.succ_ne_self k.val (congrArg Fin.val h).symm
  set σ : Equiv.Perm (Fin m) := Equiv.swap k l with hσ
  set π0 : Equiv.Perm (Fin m ⊕ Fin m) := Equiv.Perm.sumCongr σ σ with hπ0def
  have hσinv : σ⁻¹ = σ := by
    rw [hσ]
    exact Equiv.swap_inv k l
  have hπ0inv : π0⁻¹ = π0 := by
    rw [hπ0def, Equiv.Perm.sumCongr_inv, hσinv]
  have hπ0_inl (a : Fin m) : π0 (Sum.inl a) = Sum.inl (σ a) := by
    rw [hπ0def, Equiv.Perm.sumCongr_apply]
    rfl
  have hπ0_inr (a : Fin m) : π0 (Sum.inr a) = Sum.inr (σ a) := by
    rw [hπ0def, Equiv.Perm.sumCongr_apply]
    rfl
  have hσk : σ k = l := by
    rw [hσ]
    exact Equiv.swap_apply_left k l
  have hσl : σ l = k := by
    rw [hσ]
    exact Equiv.swap_apply_right k l
  have hσne {a : Fin m} (hak : a ≠ k) (hal : a ≠ l) : σ a = a := by
    rw [hσ]
    exact Equiv.swap_apply_of_ne_of_ne hak hal
  have hσkmk : σ k = ⟨k.val + 1, hk⟩ := by
    simpa [hl] using hσk
  have hσmk : σ ⟨k.val + 1, hk⟩ = k := by
    simpa [hl] using hσl
  have hkmk : k ≠ ⟨k.val + 1, hk⟩ := by
    intro h
    exact hkl (by rw [hl]; exact h)
  let u1 : Fin m ⊕ Fin m → K :=
    Pi.single (Sum.inl k) 1 + Pi.single (Sum.inl l) 1
  let u2 : Fin m ⊕ Fin m → K :=
    Pi.single (Sum.inr k) 1 + Pi.single (Sum.inr l) 1
  let g : (Fin m ⊕ Fin m → K) ≃ₗ[K] (Fin m ⊕ Fin m → K) :=
    CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m) K
      (TauCeti.permutationGL (k := K) π0)
  have hg_apply : ∀ v : Fin m ⊕ Fin m → K, g v = v ∘ ⇑π0 := by
    intro v
    change CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m) K
      (TauCeti.permutationGL (k := K) π0) v = v ∘ ⇑π0
    rw [CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply, permutationGL_mulVec, hπ0inv]
  have hcomm : CFSG.RankThree.OrthogonalInvolutions.commSpace g =
      Submodule.span K ({u1, u2} : Set (Fin m ⊕ Fin m → K)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨v, rfl⟩ := CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.mp hx
      have hv : g v - v = (v (Sum.inl l) + v (Sum.inl k)) • u1 +
          (v (Sum.inr l) + v (Sum.inr k)) • u2 := by
        funext y
        rcases y with a | a
        · by_cases hak : a = k
          · subst hak
            simp [u1, u2, hg_apply, hπ0_inl, hπ0_inr, hσk, hσl, hσkmk, hσmk, hkmk, hl, hkl, Pi.single_apply,
              sub_eq_add_neg,
              CharTwo.neg_eq, add_comm, eq_comm]
          · by_cases hal : a = l
            · subst hal
              have hkmk : k ≠ ⟨k.val + 1, hk⟩ := by simpa [hl] using hkl
              simp [u1, u2, hg_apply, hπ0_inl, hπ0_inr, hσk, hσl, hσkmk, hσmk, hkmk, hl, hkl,
                Pi.single_apply, sub_eq_add_neg, CharTwo.neg_eq, add_comm, eq_comm, hσl, hak,
                hkmk]
            · have hak' : k ≠ a := Ne.symm hak
              have hal' : a ≠ ⟨k.val + 1, hk⟩ := by simpa [hl] using hal
              simp [u1, u2, hg_apply, hπ0_inl, hπ0_inr, hσk, hσl, hσkmk, hσmk, hkmk, hl, hkl,
                Pi.single_apply, sub_eq_add_neg, CharTwo.neg_eq, add_comm, eq_comm,
                hσne hak hal, hak, hak', hal, hal']
        · by_cases hak : a = k
          · subst hak
            simp [u1, u2, hg_apply, hπ0_inl, hπ0_inr, hσk, hσl, hσkmk, hσmk, hkmk, hl, hkl, Pi.single_apply,
              sub_eq_add_neg,
              CharTwo.neg_eq, add_comm, eq_comm]
          · by_cases hal : a = l
            · subst hal
              have hkmk : k ≠ ⟨k.val + 1, hk⟩ := by simpa [hl] using hkl
              simp [u1, u2, hg_apply, hπ0_inl, hπ0_inr, hσk, hσl, hσkmk, hσmk, hkmk, hl, hkl,
                Pi.single_apply, sub_eq_add_neg, CharTwo.neg_eq, add_comm, eq_comm, hσl, hak,
                hkmk]
            · have hak' : k ≠ a := Ne.symm hak
              have hal' : a ≠ ⟨k.val + 1, hk⟩ := by simpa [hl] using hal
              simp [u1, u2, hg_apply, hπ0_inl, hπ0_inr, hσk, hσl, hσkmk, hσmk, hkmk, hl, hkl,
                Pi.single_apply, sub_eq_add_neg, CharTwo.neg_eq, add_comm, eq_comm,
                hσne hak hal, hak, hak', hal, hal']
      rw [hv]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · intro hx
      rw [Submodule.mem_span_pair] at hx
      obtain ⟨a, b, rfl⟩ := hx
      have h1 : u1 ∈ CFSG.RankThree.OrthogonalInvolutions.commSpace g := by
        rw [CFSG.RankThree.OrthogonalInvolutions.mem_commSpace]
        refine ⟨Pi.single (Sum.inl k) 1, ?_⟩
        funext y
        rcases y with c | c
        · by_cases hck : c = k
          · subst hck
            simp [u1, u2, hg_apply, hπ0_inl, hπ0_inr, hσk, hσl, hσkmk, hσmk, hkmk, hl, hkl, Pi.single_apply,
              sub_eq_add_neg,
              CharTwo.neg_eq, add_comm, eq_comm]
          · by_cases hcl : c = l
            · subst hcl
              simp [u1, u2, hg_apply, hπ0_inl, hπ0_inr, hσk, hσl, hσkmk, hσmk, hkmk, hl, hkl, Pi.single_apply,
              sub_eq_add_neg,
                CharTwo.neg_eq, add_comm, eq_comm, hσl, hck]
            · have hck' : k ≠ c := Ne.symm hck
              have hcl' : c ≠ ⟨k.val + 1, hk⟩ := by simpa [hl] using hcl
              simp [u1, u2, hg_apply, hπ0_inl, hπ0_inr, hσk, hσl, hσkmk, hσmk, hkmk, hl, hkl,
                Pi.single_apply, sub_eq_add_neg, CharTwo.neg_eq, add_comm, eq_comm,
                hσne hck hcl, hck, hck', hcl, hcl']
        · have hni : π0 (Sum.inr c) ≠ Sum.inl k := by
            rw [hπ0_inr]
            exact fun h => Sum.inl_ne_inr h.symm
          simp [u1, u2, hg_apply, hπ0_inl, hπ0_inr, hσk, hσl, hσkmk, hσmk, hkmk, hl, hkl,
            Pi.single_apply, hni, Sum.inl_ne_inr]
      have h2 : u2 ∈ CFSG.RankThree.OrthogonalInvolutions.commSpace g := by
        rw [CFSG.RankThree.OrthogonalInvolutions.mem_commSpace]
        refine ⟨Pi.single (Sum.inr k) 1, ?_⟩
        funext y
        rcases y with c | c
        · have hni : π0 (Sum.inr c) ≠ Sum.inl k := by
            rw [hπ0_inr]
            exact fun h => Sum.inl_ne_inr h.symm
          simp [u1, u2, hg_apply, hπ0_inl, hπ0_inr, hσk, hσl, hσkmk, hσmk, hkmk, hl, hkl,
            Pi.single_apply, hni, Sum.inl_ne_inr]
        · by_cases hck : c = k
          · subst hck
            simp [u1, u2, hg_apply, hπ0_inl, hπ0_inr, hσk, hσl, hσkmk, hσmk, hkmk, hl, hkl, Pi.single_apply,
              sub_eq_add_neg,
              CharTwo.neg_eq, add_comm, eq_comm]
          · by_cases hcl : c = l
            · subst hcl
              simp [u1, u2, hg_apply, hπ0_inl, hπ0_inr, hσk, hσl, hσkmk, hσmk, hkmk, hl, hkl, Pi.single_apply,
              sub_eq_add_neg,
                CharTwo.neg_eq, add_comm, eq_comm, hσl, hck]
            · have hck' : k ≠ c := Ne.symm hck
              have hcl' : c ≠ ⟨k.val + 1, hk⟩ := by simpa [hl] using hcl
              simp [u1, u2, hg_apply, hπ0_inl, hπ0_inr, hσk, hσl, hσkmk, hσmk, hkmk, hl, hkl,
                Pi.single_apply, sub_eq_add_neg, CharTwo.neg_eq, add_comm, eq_comm,
                hσne hck hcl, hck, hck', hcl, hcl']
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ h2)
  have hli : LinearIndependent K ![u1, u2] := by
    rw [linearIndependent_fin2]
    refine ⟨?_, ?_⟩
    · intro hzero
      have h := congrFun hzero (Sum.inr k)
      simp [u2, hkl, Pi.single_apply] at h
    · intro c hc
      have h1 := congrFun hc (Sum.inr k)
      have h2 := congrFun hc (Sum.inl k)
      simp [u1, u2, hkl, Pi.single_apply] at h1 h2
  have hfin : Module.finrank K (CFSG.RankThree.OrthogonalInvolutions.commSpace g) = 2 := by
    rw [hcomm]
    have hspan : Submodule.span K ({u1, u2} : Set (Fin m ⊕ Fin m → K)) =
        Submodule.span K (Set.range ![u1, u2]) := by
      congr 1
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.exists_fin_two]
      tauto
    rw [hspan, finrank_span_eq_card hli, Fintype.card_fin]
  have hPorth : TauCeti.permutationGL (k := K) π0 ∈ LargeEvenOrthGroup (LargeEvenQPlus K m) :=
    sumCongr_mem_orthPlus (K := K) σ
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (TableBOrth.qPlusForm K m) := by
    rw [largeEvenOrthGroup_def,
      CFSG.ClassicalGroups.Orthogonal.closure_isometries_eq_comap
        (Q := TableBOrth.qPlusForm K m) (Q₀ := LargeEvenQPlus K m)
        (TableBOrth.coe_qPlusForm (K := K) (m := m))] at hPorth
    exact hPorth
  have hω : g ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup
      (TableBOrth.qPlusForm K m) (TableBOrth.nondegenerate_qPlusForm (K := K) m) := by
    rw [CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup]
    exact ⟨hgO, by rw [hfin]; exact ⟨1, rfl⟩⟩
  have hT : ∃ T : Submodule K (Fin m ⊕ Fin m → K), Module.finrank K T = 3 ∧
      ∀ v ∈ T, TableBOrth.qPlusForm K m v = 0 := by
    let i0 : Fin m := ⟨0, by omega⟩
    let i1 : Fin m := ⟨1, by omega⟩
    let i2 : Fin m := ⟨2, by omega⟩
    refine CFSG.ClassicalGroups.Orthogonal.exists_totallySingular_of_hypPairs
      (Q := TableBOrth.qPlusForm K m)
      (P₁ := (TableBOrth.isHypCoord_qPlusForm (K := K) i0).hypPair)
      (P₂ := (TableBOrth.isHypCoord_qPlusForm (K := K) i1).hypPair)
      (P₃ := (TableBOrth.isHypCoord_qPlusForm (K := K) i2).hypPair) ?_ ?_ ?_
    · exact (TableBOrth.isHypCoord_qPlusForm (K := K) i0).orth
        (TableBOrth.isHypCoord_qPlusForm (K := K) i1)
        ⟨by simp [i0, i1], by simp [i0, i1], by simp [i0, i1], by simp [i0, i1]⟩
    · exact (TableBOrth.isHypCoord_qPlusForm (K := K) i0).orth
        (TableBOrth.isHypCoord_qPlusForm (K := K) i2)
        ⟨by simp [i0, i2], by simp [i0, i2], by simp [i0, i2], by simp [i0, i2]⟩
    · exact (TableBOrth.isHypCoord_qPlusForm (K := K) i1).orth
        (TableBOrth.isHypCoord_qPlusForm (K := K) i2)
        ⟨by simp [i1, i2], by simp [i1, i2], by simp [i1, i2], by simp [i1, i2]⟩
  have hmem : g ∈ CFSG.RankThree.Classical2.orthDerived (TableBOrth.qPlusForm K m) :=
    CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived
      (TableBOrth.nondegenerate_qPlusForm (K := K) m) hT hω
  have hPΩ : TauCeti.permutationGL (k := K) π0 ∈ LargeEvenOmega (LargeEvenQPlus K m) := by
    have h2 : TauCeti.permutationGL (k := K) π0 ∈
        (CFSG.RankThree.Classical2.orthDerived (TableBOrth.qPlusForm K m)).comap
          (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m) K).toMonoidHom :=
      Subgroup.mem_comap.mpr hmem
    rw [← CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap
      (Q := TableBOrth.qPlusForm K m) (Q₀ := LargeEvenQPlus K m)
      (TableBOrth.coe_qPlusForm (K := K) (m := m))] at h2
    exact h2
  exact hPΩ

theorem swapGL_mem_omega (k : Fin m) (hk : k.val + 1 < m) (hm : 3 ≤ m) :
    swapGL (K := K) (m := m) k hk ∈ LargeEvenOmega (LargeEvenQMinus m b c) := by
  change blockInl (TauCeti.permutationGL (k := K)
    (Equiv.Perm.sumCongr (Equiv.swap k ⟨k.val + 1, hk⟩)
      (Equiv.swap k ⟨k.val + 1, hk⟩))) ∈ LargeEvenOmega (LargeEvenQMinus m b c)
  exact blockInl_mem_omegaMinus b c (permutationGL_pairPerm_mem_omegaPlus (K := K) k hk hm)

theorem swapGL_conj_torusGL (k : Fin m) (hk : k.val + 1 < m) (x : Fin m → Kˣ) :
    swapGL (K := K) (m := m) k hk * torusGL K m x * (swapGL (K := K) (m := m) k hk)⁻¹ =
      torusGL K m (x ∘ Equiv.swap k ⟨k.val + 1, hk⟩) := by
  set σ : Equiv.Perm (Fin m) := Equiv.swap k ⟨k.val + 1, hk⟩ with hσdef
  have hσ : σ⁻¹ = σ := Equiv.swap_inv k ⟨k.val + 1, hk⟩
  have hblock : ∀ g d : GL (Fin m ⊕ Fin m) K,
      blockInl g * blockInl d * (blockInl g)⁻¹ = blockInl (g * d * g⁻¹) := by
    intro g d
    rw [← map_inv, ← map_mul, ← map_mul]
  change blockInl (TauCeti.permutationGL (k := K) (Equiv.Perm.sumCongr σ σ)) *
      blockInl (TauCeti.diagGL (pairedUnits x)) *
      (blockInl (TauCeti.permutationGL (k := K) (Equiv.Perm.sumCongr σ σ)))⁻¹ =
    blockInl (TauCeti.diagGL (pairedUnits (x ∘ σ)))
  rw [hblock]
  congr 1
  rw [TauCeti.mul_diagGL_of_coe_eq_permMatrix
      (TauCeti.permutationGL (k := K) (Equiv.Perm.sumCongr σ σ))
      (Equiv.Perm.sumCongr σ σ)⁻¹ (TauCeti.permutationGL_coe _)]
  rw [show TauCeti.diagGL (pairedUnits x ∘ ⇑(Equiv.Perm.sumCongr σ σ)⁻¹) *
        TauCeti.permutationGL (k := K) (Equiv.Perm.sumCongr σ σ) *
        (TauCeti.permutationGL (k := K) (Equiv.Perm.sumCongr σ σ))⁻¹ =
      TauCeti.diagGL (pairedUnits x ∘ ⇑(Equiv.Perm.sumCongr σ σ)⁻¹) from by group]
  congr 1
  rw [show (Equiv.Perm.sumCongr σ σ)⁻¹ = Equiv.Perm.sumCongr σ σ by
    rw [Equiv.Perm.sumCongr_inv, hσ]]
  funext i
  rcases i with i | i <;> rfl

@[expose] def pairVec (k : Fin m) : LargeEvenMinusIdx m → K :=
  Pi.single (Sum.inl (Sum.inl k)) 1 + Pi.single (Sum.inl (Sum.inr k)) 1

@[expose] def planeVec : LargeEvenMinusIdx m → K :=
  Pi.single (Sum.inr 0) 1

@[expose] noncomputable def planeReflGL (b : K) : GL (LargeEvenMinusIdx m) K where
  val := Matrix.fromBlocks (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
    (0 : Matrix (Fin m ⊕ Fin m) (Fin 2) K) (0 : Matrix (Fin 2) (Fin m ⊕ Fin m) K)
    (!![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) K)
  inv := Matrix.fromBlocks (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
    (0 : Matrix (Fin m ⊕ Fin m) (Fin 2) K) (0 : Matrix (Fin 2) (Fin m ⊕ Fin m) K)
    (!![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) K)
  val_inv := by
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero]
    rw [show (!![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) K) * !![1, b; 0, 1] = 1 by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]]
    simp [Matrix.fromBlocks_one, zero_add, add_zero]
  inv_val := by
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero]
    rw [show (!![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) K) * !![1, b; 0, 1] = 1 by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]]
    simp [Matrix.fromBlocks_one, zero_add, add_zero]

theorem coe_planeReflGL (b : K) :
    ((planeReflGL (K := K) (m := m) b : GL (LargeEvenMinusIdx m) K) :
      Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) =
      Matrix.fromBlocks 1 0 0 !![1, b; 0, 1] :=
  rfl

theorem qMinusForm_pairVec (k : Fin m) :
    TableBOrth.qMinusForm K m b c (pairVec (K := K) (m := m) k) = 1 := by
  rw [TableBOrth.coe_qMinusForm]
  simpa [pairVec] using TableBOrth.largeEvenQMinus_single_add_single (K := K) b c k

theorem qMinusForm_planeVec :
    TableBOrth.qMinusForm K m b c (planeVec (K := K) (m := m)) = 1 := by
  rw [TableBOrth.coe_qMinusForm]
  simp [planeVec, LargeEvenQMinus]

theorem polar_qMinusForm_pairVec (k : Fin m) (x : LargeEvenMinusIdx m → K) :
    QuadraticMap.polar (TableBOrth.qMinusForm K m b c) (pairVec (K := K) (m := m) k) x =
      x (Sum.inl (Sum.inr k)) + x (Sum.inl (Sum.inl k)) := by
  have h := TableBOrth.isHypCoord_qMinusForm (K := K) b c k
  rw [pairVec, QuadraticMap.polar_add_left, h.polar_left, h.polar_right]

theorem polar_qMinusForm_planeVec (x : LargeEvenMinusIdx m → K) :
    QuadraticMap.polar (TableBOrth.qMinusForm K m b c) (planeVec (K := K) (m := m)) x =
      b * x (Sum.inr 1) := by
  let e : (LargeEvenMinusIdx m → K) ≃ₗ[K] (Fin m ⊕ (Fin m ⊕ Fin 2) → K) :=
    TableBOrth.minusAssoc K m
  change QuadraticMap.polar ((quadMinus (m + 1) K b c).comp e.toLinearMap) planeVec x = _
  rw [TableBOrth.polar_comp_linearMap]
  have hplane : e (planeVec (K := K) (m := m)) = Pi.single (Sum.inr (Sum.inr 0)) 1 := by
    change TableBOrth.minusAssoc K m (planeVec (K := K) (m := m)) = _
    funext y
    rw [TableBOrth.minusAssoc_apply]
    rcases y with y | y | y <;> simp [planeVec, Pi.single_apply]
  have h0 : e x (Sum.inr (Sum.inr 0)) = x (Sum.inr 0) := by
    change TableBOrth.minusAssoc K m x (Sum.inr (Sum.inr 0)) = _
    rw [TableBOrth.minusAssoc_apply]
    rfl
  have h1 : e x (Sum.inr (Sum.inr 1)) = x (Sum.inr 1) := by
    change TableBOrth.minusAssoc K m x (Sum.inr (Sum.inr 1)) = _
    rw [TableBOrth.minusAssoc_apply]
    rfl
  change QuadraticMap.polar (⇑(quadMinus (m + 1) K b c)) (e planeVec) (e x) = _
  rw [hplane, QuadraticMap.polar_comm, polar_quadMinus_single_inr_inr_zero, h0, h1,
    show (2 : K) = 0 from
    CharTwo.two_eq_zero, zero_mul, zero_add]

theorem toLinEquiv_planeReflGL (b : K) :
    CFSG.ClassicalGroups.Orthogonal.toLinEquiv (LargeEvenMinusIdx m) K
        (planeReflGL (K := K) (m := m) b) =
      CFSG.ClassicalGroups.Orthogonal.reflect (TableBOrth.qMinusForm K m b c)
        (planeVec (K := K) (m := m)) := by
  have hQe := qMinusForm_planeVec (K := K) (m := m) (b := b) (c := c)
  have hpolar := polar_qMinusForm_planeVec (K := K) (m := m) (b := b) (c := c)
  have hR : ∀ x : LargeEvenMinusIdx m → K,
      CFSG.ClassicalGroups.Orthogonal.reflect (TableBOrth.qMinusForm K m b c)
        (planeVec (K := K) (m := m)) x =
        x + (b * x (Sum.inr 1)) • planeVec (K := K) (m := m) := by
    intro x
    rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply
      (by rw [hQe]; exact one_ne_zero), hQe, div_one, CharTwo.sub_eq_add]
    congr 1
    rw [hpolar]
  refine LinearEquiv.ext fun x => ?_
  rw [CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply, hR, coe_planeReflGL]
  have hmat : (Matrix.fromBlocks (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) 0 0
      (!![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) K)) *ᵥ x =
      x + (b * x (Sum.inr 1)) • planeVec (K := K) (m := m) := by
    rw [show x = Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr) from (Sum.elim_comp_inl_inr x).symm]
    rw [Matrix.fromBlocks_mulVec]
    simp only [Matrix.one_mulVec, Matrix.zero_mulVec, add_zero, zero_add, Sum.elim_comp_inl,
      Sum.elim_comp_inr, Sum.elim_comp_inl_inr]
    rw [show (!![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) K) *ᵥ (x ∘ Sum.inr) =
        ![x (Sum.inr 0) + b * x (Sum.inr 1), x (Sum.inr 1)] from by
      ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]]
    funext j
    rcases j with (j | j) | j
    · simp [planeVec, Pi.single_apply, Pi.add_apply, Pi.smul_apply, Function.comp_apply,
        smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
    · simp [planeVec, Pi.single_apply, Pi.add_apply, Pi.smul_apply, Function.comp_apply,
        smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
    · fin_cases j <;>
        simp [planeVec, Pi.single_apply, Pi.add_apply, Pi.smul_apply, Function.comp_apply,
          smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hmat]

theorem toLinEquiv_blockInl_pairSwap (k : Fin m) :
    CFSG.ClassicalGroups.Orthogonal.toLinEquiv (LargeEvenMinusIdx m) K
        (blockInl (TauCeti.permutationGL (k := K) (pairSwap k))) =
      CFSG.ClassicalGroups.Orthogonal.reflect (TableBOrth.qMinusForm K m b c)
        (pairVec (K := K) (m := m) k) := by
  have hQe := qMinusForm_pairVec (K := K) (m := m) (b := b) (c := c) k
  have hpolar := polar_qMinusForm_pairVec (K := K) (m := m) (b := b) (c := c) k
  have hR : ∀ x : LargeEvenMinusIdx m → K,
      CFSG.ClassicalGroups.Orthogonal.reflect (TableBOrth.qMinusForm K m b c)
        (pairVec (K := K) (m := m) k) x =
        x + (x (Sum.inl (Sum.inr k)) + x (Sum.inl (Sum.inl k))) •
          pairVec (K := K) (m := m) k := by
    intro x
    rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply
      (by rw [hQe]; exact one_ne_zero), hQe, div_one, CharTwo.sub_eq_add]
    congr 1
    rw [hpolar]
  have hchar1 : ∀ u v : K, u + (u + v) = v := fun u v => by
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have hchar2 : ∀ u v : K, v + (u + v) = u := fun u v => by
    rw [add_comm v (u + v), add_assoc, CharTwo.add_self_eq_zero, add_zero]
  refine LinearEquiv.ext fun x => ?_
  rw [CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply, hR, coe_blockInl]
  have hmat : (Matrix.fromBlocks
      ((TauCeti.permutationGL (k := K) (pairSwap k) : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
      (0 : Matrix (Fin m ⊕ Fin m) (Fin 2) K) (0 : Matrix (Fin 2) (Fin m ⊕ Fin m) K)
      (1 : Matrix (Fin 2) (Fin 2) K)) *ᵥ x =
      x + (x (Sum.inl (Sum.inr k)) + x (Sum.inl (Sum.inl k))) •
        pairVec (K := K) (m := m) k := by
    rw [show x = Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr) from
      (Sum.elim_comp_inl_inr x).symm]
    rw [Matrix.fromBlocks_mulVec]
    simp only [Matrix.one_mulVec, Matrix.zero_mulVec, add_zero, zero_add, Sum.elim_comp_inl,
      Sum.elim_comp_inr, Sum.elim_comp_inl_inr]
    rw [permutationGL_mulVec, pairSwap_inv]
    funext j
    rcases j with (j | j) | j
    · by_cases hj : j = k
      · subst hj
        simp [pairVec, Pi.single_apply, Function.comp_apply, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul, CharTwo.add_self_eq_zero, hchar1, hchar2, pairSwap, Equiv.swap_apply_left,
          Equiv.swap_apply_right]
      · simp [pairVec, Pi.single_apply, Function.comp_apply, pairSwap, Equiv.swap_apply_def,
          hj, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    · by_cases hj : j = k
      · subst hj
        simp [pairVec, Pi.single_apply, Function.comp_apply, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul, CharTwo.add_self_eq_zero, hchar1, hchar2, pairSwap, Equiv.swap_apply_left,
          Equiv.swap_apply_right]
      · simp [pairVec, Pi.single_apply, Function.comp_apply, pairSwap, Equiv.swap_apply_def,
          hj, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    · simp [pairVec, Pi.single_apply, Function.comp_apply, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
  rw [hmat]

theorem planeReflGL_mul_blockInl (g : GL (Fin m ⊕ Fin m) K) :
    planeReflGL (K := K) (m := m) b * blockInl g =
      blockInl g * planeReflGL (K := K) (m := m) b := by
  apply Units.ext
  ext x y
  rcases x with (x | x) | x <;> rcases y with (y | y) | y <;>
    simp [coe_blockInl, coe_planeReflGL, Matrix.fromBlocks_multiply]

@[expose] noncomputable def signGL (k : Fin m) : GL (LargeEvenMinusIdx m) K :=
  blockInl (TauCeti.permutationGL (k := K) (pairSwap k)) * planeReflGL (K := K) (m := m) b

theorem signGL_mem_omega (k : Fin m) (hm : 3 ≤ m)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    signGL (K := K) (m := m) (b := b) k ∈ LargeEvenOmega (LargeEvenQMinus m b c) := by
  let Q := TableBOrth.qMinusForm K m b c
  have hQ : (QuadraticMap.polarBilin Q).Nondegenerate :=
    TableBOrth.nondegenerate_qMinusForm (K := K) m hirr
  let i0 : Fin m := ⟨0, by omega⟩
  let i1 : Fin m := ⟨1, by omega⟩
  have hP : (TableBOrth.isHypCoord_qMinusForm (K := K) b c i0).hypPair.Orth
      (TableBOrth.isHypCoord_qMinusForm (K := K) b c i1).hypPair :=
    (TableBOrth.isHypCoord_qMinusForm (K := K) b c i0).orth
      (TableBOrth.isHypCoord_qMinusForm (K := K) b c i1)
      ⟨by simp [i0, i1], by simp [i0, i1], by simp [i0, i1], by simp [i0, i1]⟩
  obtain ⟨g, hgE, hgv⟩ :=
    CFSG.ClassicalGroups.Orthogonal.exists_mem_elementaryGroup_apply_eq
      (Q := Q) hQ
      (P := (TableBOrth.isHypCoord_qMinusForm (K := K) b c i0).hypPair)
      (P' := (TableBOrth.isHypCoord_qMinusForm (K := K) b c i1).hypPair) hP
      (x := pairVec (K := K) (m := m) k) (y := planeVec (K := K) (m := m))
      (by
        intro hzero
        have h := congrFun hzero (Sum.inl (Sum.inl k))
        simp [pairVec, Pi.single_apply] at h)
      (by
        intro hzero
        have h := congrFun hzero (Sum.inr 0)
        simp [planeVec, Pi.single_apply] at h)
      (by rw [qMinusForm_pairVec, qMinusForm_planeVec])
  let G : GL (LargeEvenMinusIdx m) K :=
    (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (LargeEvenMinusIdx m) K).symm g
  have hGlin : CFSG.ClassicalGroups.Orthogonal.toLinEquiv (LargeEvenMinusIdx m) K G = g :=
    MulEquiv.apply_symm_apply _ _
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    CFSG.ClassicalGroups.Orthogonal.elementaryGroup_le_orthogonalGroup Q hgE
  have hGO : G ∈ LargeEvenOrthGroup (LargeEvenQMinus m b c) := by
    rw [largeEvenOrthGroup_def,
      CFSG.ClassicalGroups.Orthogonal.closure_isometries_eq_comap
        (Q := Q) (Q₀ := LargeEvenQMinus m b c)
        (TableBOrth.coe_qMinusForm (K := K) (m := m) (b := b) (c := c))]
    rw [Subgroup.mem_comap]
    change CFSG.ClassicalGroups.Orthogonal.toLinEquiv (LargeEvenMinusIdx m) K G ∈ _
    rw [hGlin]
    exact hgO
  have hrO : blockInl (TauCeti.permutationGL (k := K) (pairSwap k)) ∈
      LargeEvenOrthGroup (LargeEvenQMinus m b c) := by
    rw [largeEvenOrthGroup_def,
      CFSG.ClassicalGroups.Orthogonal.closure_isometries_eq_comap
        (Q := Q) (Q₀ := LargeEvenQMinus m b c)
        (TableBOrth.coe_qMinusForm (K := K) (m := m) (b := b) (c := c))]
    rw [Subgroup.mem_comap]
    change CFSG.ClassicalGroups.Orthogonal.toLinEquiv (LargeEvenMinusIdx m) K
      (blockInl (TauCeti.permutationGL (k := K) (pairSwap k))) ∈ _
    rw [toLinEquiv_blockInl_pairSwap]
    exact CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup _ _
  have hcomm_rs : blockInl (TauCeti.permutationGL (k := K) (pairSwap k)) *
      planeReflGL (K := K) (m := m) b =
      planeReflGL (K := K) (m := m) b *
        blockInl (TauCeti.permutationGL (k := K) (pairSwap k)) :=
    (planeReflGL_mul_blockInl (K := K) (m := m) (b := b)
      (TauCeti.permutationGL (k := K) (pairSwap k))).symm
  have key : CFSG.ClassicalGroups.Orthogonal.toLinEquiv (LargeEvenMinusIdx m) K
      (⁅G, blockInl (TauCeti.permutationGL (k := K) (pairSwap k))⁆) =
      CFSG.ClassicalGroups.Orthogonal.toLinEquiv (LargeEvenMinusIdx m) K
        (blockInl (TauCeti.permutationGL (k := K) (pairSwap k)) *
          planeReflGL (K := K) (m := m) b) := by
    rw [map_commutatorElement, hGlin, toLinEquiv_blockInl_pairSwap, commutatorElement_def,
      CFSG.ClassicalGroups.Orthogonal.reflect_inv,
      CFSG.ClassicalGroups.Orthogonal.reflect_conj hgO (pairVec (K := K) (m := m) k), hgv]
    rw [hcomm_rs, map_mul, toLinEquiv_planeReflGL, toLinEquiv_blockInl_pairSwap]
  have hsign : ⁅G, blockInl (TauCeti.permutationGL (k := K) (pairSwap k))⁆ =
      signGL (K := K) (m := m) (b := b) k :=
    (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (LargeEvenMinusIdx m) K).injective key
  rw [← hsign]
  exact Subgroup.commutator_mem_commutator hGO hrO

theorem signGL_conj_torusGL (k : Fin m) (x : Fin m → Kˣ) :
    signGL (K := K) (m := m) (b := b) k * torusGL K m x *
        (signGL (K := K) (m := m) (b := b) k)⁻¹ =
      torusGL K m (Function.update x k (x k)⁻¹) := by
  have hblock : ∀ g d : GL (Fin m ⊕ Fin m) K,
      blockInl g * blockInl d * (blockInl g)⁻¹ = blockInl (g * d * g⁻¹) := by
    intro g d
    rw [← map_inv, ← map_mul, ← map_mul]
  have hcomm_sT : planeReflGL (K := K) (m := m) b * torusGL K m x =
      torusGL K m x * planeReflGL (K := K) (m := m) b := by
    rw [torusGL_apply]
    exact planeReflGL_mul_blockInl (K := K) (m := m) (b := b)
      (TauCeti.diagGL (pairedUnits x))
  change (blockInl (TauCeti.permutationGL (k := K) (pairSwap k)) *
        planeReflGL (K := K) (m := m) b) * torusGL K m x *
      (blockInl (TauCeti.permutationGL (k := K) (pairSwap k)) *
        planeReflGL (K := K) (m := m) b)⁻¹ =
    torusGL K m (Function.update x k (x k)⁻¹)
  rw [_root_.mul_inv_rev]
  calc
    (blockInl (TauCeti.permutationGL (k := K) (pairSwap k)) *
        planeReflGL (K := K) (m := m) b) * torusGL K m x *
        ((planeReflGL (K := K) (m := m) b)⁻¹ *
          (blockInl (TauCeti.permutationGL (k := K) (pairSwap k)))⁻¹)
      = blockInl (TauCeti.permutationGL (k := K) (pairSwap k)) *
          (planeReflGL (K := K) (m := m) b * torusGL K m x *
            (planeReflGL (K := K) (m := m) b)⁻¹) *
          (blockInl (TauCeti.permutationGL (k := K) (pairSwap k)))⁻¹ := by group
    _ = blockInl (TauCeti.permutationGL (k := K) (pairSwap k)) * torusGL K m x *
          (blockInl (TauCeti.permutationGL (k := K) (pairSwap k)))⁻¹ := by
        rw [show planeReflGL (K := K) (m := m) b * torusGL K m x *
              (planeReflGL (K := K) (m := m) b)⁻¹ = torusGL K m x from by
            rw [hcomm_sT, mul_assoc, mul_inv_cancel, mul_one]]
    _ = blockInl (TauCeti.permutationGL (k := K) (pairSwap k) *
          TauCeti.diagGL (pairedUnits x) *
          (TauCeti.permutationGL (k := K) (pairSwap k))⁻¹) := by
        change blockInl (TauCeti.permutationGL (k := K) (pairSwap k)) *
          blockInl (TauCeti.diagGL (pairedUnits x)) *
          (blockInl (TauCeti.permutationGL (k := K) (pairSwap k)))⁻¹ = _
        exact hblock _ _
    _ = blockInl (TauCeti.diagGL (pairedUnits (Function.update x k (x k)⁻¹))) := by
        congr 1
        rw [TauCeti.mul_diagGL_of_coe_eq_permMatrix
          (TauCeti.permutationGL (k := K) (pairSwap k)) (pairSwap k)⁻¹
          (TauCeti.permutationGL_coe _)]
        rw [show TauCeti.diagGL (pairedUnits x ∘ ⇑(pairSwap k)⁻¹) *
              TauCeti.permutationGL (k := K) (pairSwap k) *
              (TauCeti.permutationGL (k := K) (pairSwap k))⁻¹ =
            TauCeti.diagGL (pairedUnits x ∘ ⇑(pairSwap k)⁻¹) from by group]
        congr 1
        rw [pairSwap_inv, pairedUnits_comp_pairSwap]
    _ = torusGL K m (Function.update x k (x k)⁻¹) := by rw [torusGL_apply]

@[expose] noncomputable def swap (k : Fin m) (hk : k.val + 1 < m) (hm : 3 ≤ m) :
    ↥(LargeEvenOmega (LargeEvenQMinus m b c)) :=
  ⟨swapGL (K := K) (m := m) k hk,
    swapGL_mem_omega (K := K) (m := m) (b := b) (c := c) k hk hm⟩

theorem coe_swap (k : Fin m) (hk : k.val + 1 < m) (hm : 3 ≤ m) :
    (swap (K := K) (m := m) (b := b) (c := c) k hk hm :
      GL (LargeEvenMinusIdx m) K) = swapGL (K := K) (m := m) k hk :=
  rfl

theorem swap_conj_torus (k : Fin m) (hk : k.val + 1 < m) (hm : 3 ≤ m)
    (x : Fin m → Kˣ) :
    swap (K := K) (m := m) (b := b) (c := c) k hk hm * torus x *
        (swap (K := K) (m := m) (b := b) (c := c) k hk hm)⁻¹ =
      torus (x ∘ Equiv.swap k ⟨k.val + 1, hk⟩) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_swap, coe_torus]
  exact swapGL_conj_torusGL k hk x

@[expose] noncomputable def sign (k : Fin m) (hm : 3 ≤ m)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ↥(LargeEvenOmega (LargeEvenQMinus m b c)) :=
  ⟨signGL (K := K) (m := m) (b := b) k,
    signGL_mem_omega (K := K) (m := m) (b := b) (c := c) k hm hirr⟩

theorem coe_sign (k : Fin m) (hm : 3 ≤ m)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (sign (K := K) (m := m) (b := b) (c := c) k hm hirr :
      GL (LargeEvenMinusIdx m) K) = signGL (K := K) (m := m) (b := b) k :=
  rfl

theorem sign_conj_torus (k : Fin m) (hm : 3 ≤ m)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (x : Fin m → Kˣ) :
    sign (K := K) (m := m) (b := b) (c := c) k hm hirr * torus x *
        (sign (K := K) (m := m) (b := b) (c := c) k hm hirr)⁻¹ =
      torus (Function.update x k (x k)⁻¹) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_sign, coe_torus]
  exact signGL_conj_torusGL k x
