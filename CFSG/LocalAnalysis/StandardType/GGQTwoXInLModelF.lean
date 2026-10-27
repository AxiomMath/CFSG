module

public import CFSG.LocalAnalysis.StandardType.GGQTwoInputs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLDType
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLModelFData

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggQTwoXInL_model_formed {G : Type} [Group G] (n : ℕ) (hn6 : 6 ≤ n)
    {Bs : Subgroup G} {x y : G} {D L J K : Subgroup G} (hx : x ∈ Bs) (hy : y ∈ Bs)
    (ι : Additive ↥Bs ≃+ (Fin n → ZMod 3))
    (hL : (ggAutomizer L Bs).map (ggLin (p := 3) ι) =
      Subgroup.closure {T | ∃ σ : Equiv.Perm (Fin n), ∀ (v : Fin n → ZMod 3) (i : Fin n),
        T v i = v (σ i)})
    (hK : (ggAutomizer K Bs).map (ggLin (p := 3) ι) =
      Subgroup.closure {T | ∃ σ : Equiv.Perm (Fin n), ∀ (v : Fin n → ZMod 3) (i : Fin n),
        T v i = ((if i.val = 0 then (-1 : ZMod 3) else 1) *
          (if (σ i).val = 0 then (-1 : ZMod 3) else 1)) * v (σ i)})
    (hxv : ι (Additive.ofMul ⟨x, hx⟩) = fun _ => 1)
    (hyv : ι (Additive.ofMul ⟨y, hy⟩) = fun i => if i.val = 0 then (-1 : ZMod 3) else 1) :
    Nonempty (GGQTwoModel 3 Bs x y D L J K) := by
  cases n with
  | zero => omega
  | succ m =>
    have hm2 : 2 ≤ m + 1 := by omega
    have hadj : Subgroup.closure (Set.range (fun l : Fin m =>
        Equiv.swap l.castSucc l.succ)) = ⊤ :=
      Subgroup.closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ m)
    have hclP : Subgroup.closure (Set.range ⇑(q3f_P (m + 1))) = (q3f_P (m + 1)).range := by
      apply le_antisymm
      · rw [Subgroup.closure_le]
        rintro T ⟨σ, rfl⟩
        exact MonoidHom.mem_range.mpr ⟨σ, rfl⟩
      · intro T hT
        obtain ⟨σ, rfl⟩ := MonoidHom.mem_range.mp hT
        exact Subgroup.subset_closure ⟨σ, rfl⟩
    have hmapL : Subgroup.map (ggLin (p := 3) ι) (ggAutomizer L Bs) =
        (q3f_P (m + 1)).range := by
      rw [hL]
      have hset : {T : (Fin (m + 1) → ZMod 3) ≃ₗ[ZMod 3] (Fin (m + 1) → ZMod 3) |
          ∃ σ : Equiv.Perm (Fin (m + 1)), ∀ (v : Fin (m + 1) → ZMod 3) (i : Fin (m + 1)),
            T v i = v (σ i)} = Set.range ⇑(q3f_P (m + 1)) := by
        ext T; constructor
        · rintro ⟨σ, hσ⟩
          refine ⟨σ.symm, ?_⟩
          ext v i
          rw [hσ v i]
          rfl
        · rintro ⟨σ, rfl⟩
          exact ⟨σ.symm, fun v i => rfl⟩
      rw [hset, hclP]
    have hmapK : Subgroup.map (ggLin (p := 3) ι) (ggAutomizer K Bs) =
        (q3f_P (m + 1)).range.map (q3f_conjD (m + 1)).toMonoidHom := by
      rw [hK]
      have hset : {T : (Fin (m + 1) → ZMod 3) ≃ₗ[ZMod 3] (Fin (m + 1) → ZMod 3) |
          ∃ σ : Equiv.Perm (Fin (m + 1)), ∀ (v : Fin (m + 1) → ZMod 3) (i : Fin (m + 1)),
            T v i = ((if i.val = 0 then (-1 : ZMod 3) else 1) *
              (if (σ i).val = 0 then (-1 : ZMod 3) else 1)) * v (σ i)} =
          Set.range (fun σ : Equiv.Perm (Fin (m + 1)) =>
            q3f_conjD (m + 1) (q3f_P (m + 1) σ)) := by
        ext T; constructor
        · rintro ⟨σ, hσ⟩
          refine ⟨σ.symm, ?_⟩
          ext v i
          rw [hσ v i]
          simp only [q3f_conjD_apply, q3f_P_apply, q3f_permLin_apply, LinearEquiv.mul_apply,
            q3f_dLin_apply, Function.comp_apply, smul_eq_mul, Equiv.symm_symm]
          ring_nf
        · rintro ⟨σ, rfl⟩
          refine ⟨σ.symm, fun v i => ?_⟩
          simp only [q3f_conjD_apply, q3f_P_apply, q3f_permLin_apply, LinearEquiv.mul_apply,
            q3f_dLin_apply, Function.comp_apply, smul_eq_mul, Equiv.symm_symm]
          ring_nf
      rw [hset]
      rw [show Set.range (fun σ : Equiv.Perm (Fin (m + 1)) =>
            q3f_conjD (m + 1) (q3f_P (m + 1) σ)) =
          q3f_conjD (m + 1) '' Set.range ⇑(q3f_P (m + 1)) from by
        ext X; constructor
        · rintro ⟨σ, rfl⟩; exact ⟨q3f_P (m + 1) σ, ⟨σ, rfl⟩, rfl⟩
        · rintro ⟨Y, ⟨σ, rfl⟩, rfl⟩; exact ⟨σ, rfl⟩]
      have hmc := MonoidHom.map_closure (q3f_conjD (m + 1)).toMonoidHom
        (Set.range ⇑(q3f_P (m + 1)))
      rw [hclP] at hmc
      exact hmc.symm
    have hgenL : Subgroup.closure
        (Set.range (fun i : {i : Fin (m + 1) // i ≠ q3f_av m} =>
          q3f_r (m + 1) hm2 i.1)) = (q3f_P (m + 1)).range := by
      apply le_antisymm
      · rw [Subgroup.closure_le]
        rintro X ⟨i, rfl⟩
        show q3f_r (m + 1) hm2 i.1 ∈ (q3f_P (m + 1)).range
        rw [q3f_r, if_neg (q3f_ne_av _ i.2)]
        exact MonoidHom.mem_range.mpr ⟨q3f_tau (m + 1) hm2 i.1, rfl⟩
      · rw [show (q3f_P (m + 1)).range = Subgroup.map (q3f_P (m + 1))
            (Subgroup.closure (Set.range (fun l : Fin m =>
              Equiv.swap l.castSucc l.succ))) from by
          rw [hadj, Subgroup.map_top]]
        rw [MonoidHom.map_closure]
        apply Subgroup.closure_mono
        rintro X ⟨Y, ⟨l, rfl⟩, rfl⟩
        refine ⟨q3f_index m l, ?_⟩
        show q3f_r (m + 1) hm2 (q3f_index m l).1 = q3f_P (m + 1) (Equiv.swap l.castSucc l.succ)
        rw [q3f_r, if_neg (q3f_ne_av _ (q3f_index m l).2), q3f_tau_index m l]
    have hgenK : Subgroup.closure
        (Set.range (fun i : {i : Fin (m + 1) // i ≠ q3f_bv m} =>
          q3f_r (m + 1) hm2 i.1)) =
        (q3f_P (m + 1)).range.map (q3f_conjD (m + 1)).toMonoidHom := by
      apply le_antisymm
      · rw [Subgroup.closure_le]
        rintro X ⟨i, rfl⟩
        show q3f_r (m + 1) hm2 i.1 ∈ (q3f_P (m + 1)).range.map (q3f_conjD (m + 1)).toMonoidHom
        rw [q3f_r_eq_conjD (m + 1) hm2 i.1 (q3f_ne_bv _ i.2)]
        exact Subgroup.mem_map.mpr ⟨q3f_P (m + 1) (q3f_tau (m + 1) hm2 i.1),
          MonoidHom.mem_range.mpr ⟨_, rfl⟩, rfl⟩
      · intro X hX
        rcases Subgroup.mem_map.mp hX with ⟨Y, hY, rfl⟩
        obtain ⟨σ, rfl⟩ := MonoidHom.mem_range.mp hY
        have hσ : σ ∈ Subgroup.closure (Set.range (fun l : Fin m =>
            Equiv.swap l.castSucc l.succ)) := by rw [hadj]; exact Subgroup.mem_top σ
        have h1 : (q3f_conjD (m + 1)).toMonoidHom ((q3f_P (m + 1)) σ) ∈
            Subgroup.map ((q3f_conjD (m + 1)).toMonoidHom.comp (q3f_P (m + 1)))
              (Subgroup.closure (Set.range (fun l : Fin m =>
                Equiv.swap l.castSucc l.succ))) :=
          Subgroup.mem_map.mpr ⟨σ, hσ, rfl⟩
        rw [MonoidHom.map_closure] at h1
        refine Subgroup.closure_mono ?_ h1
        rintro X ⟨Y, ⟨l, rfl⟩, rfl⟩
        refine ⟨q3f_indexK m l, ?_⟩
        show q3f_r (m + 1) hm2 (q3f_indexK m l).1 =
          q3f_conjD (m + 1) (q3f_P (m + 1) (Equiv.swap l.castSucc l.succ))
        rw [q3f_r_eq_conjD (m + 1) hm2 (q3f_indexK m l).1 (q3f_ne_bv _ (q3f_indexK m l).2),
          q3f_tau_indexK m l]
    have hsimple : ∀ i : Fin (m + 1), ∃ φ : MulAut ↥Bs,
        ggLin (p := 3) ι φ = q3f_r (m + 1) hm2 i := by
      intro i
      by_cases hia : i.val = m + 1 - 2
      · have hmem : q3f_r (m + 1) hm2 i ∈
            Subgroup.map (ggLin (p := 3) ι) (ggAutomizer K Bs) := by
          rw [hmapK]
          refine Subgroup.mem_map.mpr ⟨q3f_P (m + 1) (q3f_tau (m + 1) hm2 i),
            MonoidHom.mem_range.mpr ⟨_, rfl⟩, ?_⟩
          change q3f_conjD (m + 1) (q3f_P (m + 1) (q3f_tau (m + 1) hm2 i)) =
            q3f_r (m + 1) hm2 i
          rw [q3f_r, if_pos hia]
        rcases hmem with ⟨φ, hφ, hφeq⟩
        exact ⟨φ, hφeq⟩
      · have hmem : q3f_r (m + 1) hm2 i ∈
            Subgroup.map (ggLin (p := 3) ι) (ggAutomizer L Bs) := by
          rw [hmapL]
          refine MonoidHom.mem_range.mpr ⟨q3f_tau (m + 1) hm2 i, ?_⟩
          rw [q3f_r, if_neg hia]
        rcases hmem with ⟨φ, hφ, hφeq⟩
        exact ⟨φ, hφeq⟩
    let simple : Fin (m + 1) → MulAut ↥Bs := fun i => Classical.choose (hsimple i)
    have hsimple_spec : ∀ i, ggLin (p := 3) ι (simple i) = q3f_r (m + 1) hm2 i :=
      fun i => Classical.choose_spec (hsimple i)
    have hautL : ggAutomizer L Bs = Subgroup.closure (simple '' {k | k ≠ q3f_av m}) := by
      apply Subgroup.map_injective (ggLin_injective (p := 3) ι)
      rw [hmapL, MonoidHom.map_closure]
      rw [show ggLin (p := 3) ι '' (simple '' {k : Fin (m + 1) | k ≠ q3f_av m}) =
          Set.range (fun i : {i : Fin (m + 1) // i ≠ q3f_av m} =>
            q3f_r (m + 1) hm2 i.1) from by
        ext X; constructor
        · rintro ⟨Y, ⟨k, hk, rfl⟩, rfl⟩
          exact ⟨⟨k, hk⟩, (hsimple_spec k).symm⟩
        · rintro ⟨i, rfl⟩
          exact ⟨simple i.1, ⟨i.1, i.2, rfl⟩, hsimple_spec i.1⟩]
      exact hgenL.symm
    have hautK : ggAutomizer K Bs = Subgroup.closure (simple '' {k | k ≠ q3f_bv m}) := by
      apply Subgroup.map_injective (ggLin_injective (p := 3) ι)
      rw [hmapK, MonoidHom.map_closure]
      rw [show ggLin (p := 3) ι '' (simple '' {k : Fin (m + 1) | k ≠ q3f_bv m}) =
          Set.range (fun i : {i : Fin (m + 1) // i ≠ q3f_bv m} =>
            q3f_r (m + 1) hm2 i.1) from by
        ext X; constructor
        · rintro ⟨Y, ⟨k, hk, rfl⟩, rfl⟩
          exact ⟨⟨k, hk⟩, (hsimple_spec k).symm⟩
        · rintro ⟨i, rfl⟩
          exact ⟨simple i.1, ⟨i.1, i.2, rfl⟩, hsimple_spec i.1⟩]
      exact hgenK.symm
    have hfixX : ggFixedSubmodule (p := 3) ι (ggAutomizer L Bs) =
        Submodule.span (ZMod 3) {q3f_one (m + 1)} := by
      apply le_antisymm
      · intro v hv
        rw [Submodule.mem_span_singleton]
        have hall : ∀ σ : Equiv.Perm (Fin (m + 1)), q3f_P (m + 1) σ v = v := by
          intro σ
          have hmem : q3f_P (m + 1) σ ∈
              Subgroup.map (ggLin (p := 3) ι) (ggAutomizer L Bs) := by
            rw [hmapL]; exact MonoidHom.mem_range.mpr ⟨σ, rfl⟩
          rcases hmem with ⟨φ, hφ, hφeq⟩
          rw [← hφeq]
          exact (mem_ggFixedSubmodule_iff.mp hv) φ hφ
        obtain ⟨c, hc⟩ := (q3f_mem_fixed_range_P (m + 1) (by omega) v).mp hall
        exact ⟨c, by rw [hc]⟩
      · intro v hv
        rw [Submodule.mem_span_singleton] at hv
        obtain ⟨c, rfl⟩ := hv
        rw [mem_ggFixedSubmodule_iff]
        intro φ hφ
        have hmem : ggLin (p := 3) ι φ ∈
            Subgroup.map (ggLin (p := 3) ι) (ggAutomizer L Bs) := ⟨φ, hφ, rfl⟩
        rw [hmapL] at hmem
        obtain ⟨σ, hσ⟩ := MonoidHom.mem_range.mp hmem
        rw [← hσ, map_smul, q3f_P_one]
    have hfixY : ggFixedSubmodule (p := 3) ι (ggAutomizer K Bs) =
        Submodule.span (ZMod 3) {q3f_dLin (m + 1) (q3f_one (m + 1))} := by
      apply le_antisymm
      · intro v hv
        rw [Submodule.mem_span_singleton]
        have hall : ∀ σ : Equiv.Perm (Fin (m + 1)),
            q3f_P (m + 1) σ (q3f_dLin (m + 1) v) = q3f_dLin (m + 1) v := by
          intro σ
          have hmem : q3f_conjD (m + 1) (q3f_P (m + 1) σ) ∈
              Subgroup.map (ggLin (p := 3) ι) (ggAutomizer K Bs) := by
            rw [hmapK]
            exact Subgroup.mem_map.mpr ⟨q3f_P (m + 1) σ,
              MonoidHom.mem_range.mpr ⟨σ, rfl⟩, rfl⟩
          rcases hmem with ⟨φ, hφ, hφeq⟩
          have hfix := (mem_ggFixedSubmodule_iff.mp hv) φ hφ
          rw [hφeq, q3f_conjD_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply] at hfix
          have h2 := congrArg (q3f_dLin (m + 1)) hfix
          rw [q3f_dLin_involutive] at h2
          exact h2
        obtain ⟨c, hc⟩ := (q3f_mem_fixed_range_P (m + 1) (by omega)
          (q3f_dLin (m + 1) v)).mp hall
        refine ⟨c, ?_⟩
        symm
        calc v = q3f_dLin (m + 1) (q3f_dLin (m + 1) v) := (q3f_dLin_involutive (m + 1) v).symm
          _ = q3f_dLin (m + 1) (c • q3f_one (m + 1)) := by rw [hc]
          _ = c • q3f_dLin (m + 1) (q3f_one (m + 1)) := by rw [map_smul]
      · intro v hv
        rw [Submodule.mem_span_singleton] at hv
        obtain ⟨c, rfl⟩ := hv
        rw [mem_ggFixedSubmodule_iff]
        intro φ hφ
        have hmem : ggLin (p := 3) ι φ ∈
            Subgroup.map (ggLin (p := 3) ι) (ggAutomizer K Bs) := ⟨φ, hφ, rfl⟩
        rw [hmapK] at hmem
        rcases Subgroup.mem_map.mp hmem with ⟨X, hX, hXeq⟩
        obtain ⟨σ, hσ⟩ := MonoidHom.mem_range.mp hX
        rw [← hXeq, ← hσ]
        change (q3f_conjD (m + 1) (q3f_P (m + 1) σ))
          (c • q3f_dLin (m + 1) (q3f_one (m + 1))) = c • q3f_dLin (m + 1) (q3f_one (m + 1))
        rw [q3f_conjD_apply]
        have hDD1 : q3f_dLin (m + 1) (q3f_dLin (m + 1) (q3f_one (m + 1))) =
            q3f_one (m + 1) := by
          rw [← LinearEquiv.mul_apply, q3f_dLin_mul_self]
          rfl
        have hPone : q3f_P (m + 1) σ (q3f_one (m + 1)) = q3f_one (m + 1) := q3f_P_one (m + 1) σ
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, map_smul, map_smul, map_smul,
          hDD1, hPone]
    refine ⟨{
      ι := Fin (m + 1)
      instFintype := inferInstance
      instDecEq := inferInstance
      coxeter := ggCoxeterMatrixD (m + 1)
      cartan := CartanMatrix.D (m + 1)
      V := Fin (m + 1) → ZMod 3
      instAddCommGroup := inferInstance
      instModule := inferInstance
      model := ι
      hx := hx
      hy := hy
      simple := simple
      coroot := q3f_coroot (m + 1)
      root := q3f_root (m + 1)
      a := q3f_av m
      b := q3f_bv m
      a_ne_b := by simp only [q3f_av, q3f_bv, ne_eq, Fin.mk.injEq]; omega
      a_leaf := by
        refine ⟨⟨m - 2, by omega⟩, ⟨?_, ?_⟩, ?_⟩
        · simp only [q3f_av, ne_eq, Fin.mk.injEq]; omega
        · exact (q3f_D_av m (by omega) ⟨m - 2, by omega⟩ (by
            simp only [q3f_av, ne_eq, Fin.mk.injEq]; omega)).mpr rfl
        · intro c hc
          exact (q3f_D_av m (by omega) c hc.1).mp hc.2
      isWeyl := by
        refine Or.inl ⟨m + 1, Equiv.refl _, by omega, Or.inr (Or.inr ⟨by omega, ?_⟩)⟩
        apply CoxeterMatrix.ext
        funext i j
        rw [CoxeterMatrix.reindex_apply]
        rfl
      isCartan := ggIntCartan_D (m + 1)
      pairing := q3f_pairing (m + 1) (by omega)
      simple_apply := by
        intro i w
        rw [hsimple_spec i]
        exact q3f_r_apply (m + 1) hm2 i w
      automizer_L := hautL
      automizer_K := hautK
      fixed_x := by rw [hxv]; exact hfixX
      fixed_y := by
        rw [hyv]
        rw [show (fun i : Fin (m + 1) => if i.val = 0 then (-1 : ZMod 3) else 1) =
            q3f_dLin (m + 1) (q3f_one (m + 1)) from by
          ext i; simp [q3f_dLin, q3f_one]]
        exact hfixY }⟩

end CFSG.StandardType

end
