module

public import CFSG.LocalAnalysis.StandardType.FF81.CentAModelDefs
import CFSG.LocalAnalysis.StandardType.FF81.CentAModelAut
import CFSG.LocalAnalysis.StandardType.FF81.CentAModelUnip
import CFSG.LocalAnalysis.StandardType.FF81.RootFusionLinModule

public section

namespace CFSG.StandardType.FF81.CentA

open Matrix RootFusionLin

private theorem caRAut_sigmaStd_apply (m : ℕ) (g : GL (BlkIdx 1 m) (ZMod 2)) :
    sigmaStd m g = antiDiag m * Matrix.GeneralLinearGroup.inverseTranspose g * (antiDiag m)⁻¹ := by
  rw [sigmaStd, MulAut.mul_apply, MulAut.conj_apply]

theorem exists_cent_eq_conj_sigmaStd {m : ℕ} (α : MulAut (GL (BlkIdx 1 m) (ZMod 2)))
    {A : GL (BlkIdx 1 m) (ZMod 2)}
    (hA : ∀ g, α g = A * Matrix.GeneralLinearGroup.inverseTranspose g * A⁻¹)
    (hJ : α (jGL 1 m) = jGL 1 m) :
    ∃ y ∈ Cent 1 m, ∀ g, α g = y * sigmaStd m g * y⁻¹ := by
  have hAJ : A * Matrix.GeneralLinearGroup.inverseTranspose (jGL 1 m) * A⁻¹ = jGL 1 m := by
    rw [← hA (jGL 1 m)]
    exact hJ
  have hSJ : antiDiag m * Matrix.GeneralLinearGroup.inverseTranspose (jGL 1 m) *
      (antiDiag m)⁻¹ = jGL 1 m := by
    rw [← caRAut_sigmaStd_apply m (jGL 1 m)]
    exact sigmaStd_jGL m
  refine ⟨A * (antiDiag m)⁻¹, ?_, ?_⟩
  · rw [Cent, Subgroup.mem_centralizer_singleton_iff]
    calc A * (antiDiag m)⁻¹ * jGL 1 m
        = A * (antiDiag m)⁻¹ *
            (antiDiag m * Matrix.GeneralLinearGroup.inverseTranspose (jGL 1 m) *
              (antiDiag m)⁻¹) := by rw [hSJ]
      _ = A * Matrix.GeneralLinearGroup.inverseTranspose (jGL 1 m) * (antiDiag m)⁻¹ := by group
      _ = (A * Matrix.GeneralLinearGroup.inverseTranspose (jGL 1 m) * A⁻¹) *
            (A * (antiDiag m)⁻¹) := by group
      _ = jGL 1 m * (A * (antiDiag m)⁻¹) := by rw [hAJ]
  · intro g
    rw [hA g, caRAut_sigmaStd_apply m g]
    group

private theorem caRAut_conj_uSub_uGL {m : ℕ} {u : GL (BlkIdx 1 m) (ZMod 2)} (hu : u ∈ uSub 1 m)
    (b : Matrix (Fin m) (Fin 1) (ZMod 2)) (c : Matrix (Fin 1) (Fin 1) (ZMod 2)) :
    ∃ c' : Matrix (Fin 1) (Fin 1) (ZMod 2), u * uGL 0 b c * u⁻¹ = uGL 0 b c' := by
  obtain ⟨a, b', c'', rfl⟩ := hu
  refine ⟨a * b + c, ?_⟩
  have h := uGL_commutator 1 m a 0 b' b c'' c
  rw [show a * b + (0 : Matrix (Fin 1) (Fin m) (ZMod 2)) * b' = a * b from by simp] at h
  have hcomm : uGL a b' c'' * uGL 0 b c * (uGL a b' c'')⁻¹ =
      uGL 0 0 (a * b) * uGL 0 b c := by
    calc uGL a b' c'' * uGL 0 b c * (uGL a b' c'')⁻¹
        = (uGL a b' c'' * uGL 0 b c * (uGL a b' c'')⁻¹ * (uGL 0 b c)⁻¹) *
            uGL 0 b c := by group
      _ = uGL 0 0 (a * b) * uGL 0 b c := by rw [h]
  rw [hcomm, uGL_mul]
  simp

theorem exists_inner_of_fix_jGL {k : ℕ} (hk : 3 ≤ k) (α : MulAut (GL (BlkIdx 1 k) (ZMod 2)))
    (hJ : α (jGL 1 k) = jGL 1 k) (hU : ∀ g ∈ Cent 1 k, α g * g⁻¹ ∈ uSub 1 k) :
    ∃ a : GL (BlkIdx 1 k) (ZMod 2), ∀ g, α g = a * g * a⁻¹ := by
  obtain ⟨A, hA | hA⟩ := exists_eq_conj_or_conj_inverseTranspose (by omega : 1 ≤ k) α
  · exact ⟨A, hA⟩
  · exfalso
    obtain ⟨y, hyC, hy⟩ := exists_cent_eq_conj_sigmaStd α hA hJ
    have huOne_uTwo : ∀ u ∈ uOne k, α u ∈ uTwo k := by
      intro u hu
      have h1 : sigmaStd k u ∈ uTwo k := by
        rw [← sigmaStd_map_uOne]
        exact Subgroup.mem_map_of_mem (sigmaStd k).toMonoidHom hu
      have h2 : y * sigmaStd k u * y⁻¹ ∈ uTwo k := conj_mem_uTwo hyC h1
      rw [hy u]
      exact h2
    let W : AddSubgroup (Matrix (Fin 1) (Fin k) (ZMod 2) × Matrix (Fin k) (Fin 1) (ZMod 2)) :=
      { carrier := {w | ∃ (c : Matrix (Fin 1) (Fin 1) (ZMod 2))
            (c' : Matrix (Fin 1) (Fin 1) (ZMod 2)), α (uGL w.1 0 c) = uGL 0 w.2 c'}
        zero_mem' := ⟨0, 0, by simp [uGL_zero]⟩
        add_mem' := by
          rintro ⟨a, b⟩ ⟨a', b'⟩ ⟨c, c', hc⟩ ⟨d, d', hd⟩
          rw [Prod.mk_add_mk]
          refine ⟨c + d, c' + d', ?_⟩
          have h1 : (uGL (a + a') 0 (c + d) : GL (BlkIdx 1 k) (ZMod 2)) =
              uGL a 0 c * uGL a' 0 d := by
            rw [uGL_mul]
            simp
          have h2 : (uGL 0 (b + b') (c' + d') : GL (BlkIdx 1 k) (ZMod 2)) =
              uGL 0 b c' * uGL 0 b' d' := by
            rw [uGL_mul]
            simp
          rw [h1, map_mul, hc, hd, ← h2]
        neg_mem' := by
          rintro ⟨a, b⟩ ⟨c, c', hc⟩
          refine ⟨c, c', ?_⟩
          change α (uGL (-a) 0 c) = uGL 0 (-b) c'
          rw [show (-a : Matrix (Fin 1) (Fin k) (ZMod 2)) = a from by
                ext i j; exact ZMod.neg_eq_self_mod_two _,
              show (-b : Matrix (Fin k) (Fin 1) (ZMod 2)) = b from by
                ext i j; exact ZMod.neg_eq_self_mod_two _]
          exact hc }
    have hW : ∀ (P : GL (Fin 1) (ZMod 2)) (R : GL (Fin k) (ZMod 2)),
        ∀ w ∈ W, (actA 1 k P R w.1, actB 1 k P R w.2) ∈ W := by
      rintro P R ⟨a, b⟩ ⟨c, c', hc⟩
      obtain ⟨u', hu', hu'eq⟩ : ∃ u' ∈ uSub 1 k, α (levi P R) = u' * levi P R :=
        ⟨α (levi P R) * (levi P R)⁻¹, hU _ (levi_mem_cent 1 k P R), by group⟩
      obtain ⟨c₂, hc₂⟩ := caRAut_conj_uSub_uGL hu' (actB 1 k P R b)
        ((P : Matrix (Fin 1) (Fin 1) (ZMod 2)) * c' *
          ((P⁻¹ : GL (Fin 1) (ZMod 2)) : Matrix (Fin 1) (Fin 1) (ZMod 2)))
      refine ⟨(P : Matrix (Fin 1) (Fin 1) (ZMod 2)) * c *
        ((P⁻¹ : GL (Fin 1) (ZMod 2)) : Matrix (Fin 1) (Fin 1) (ZMod 2)), c₂, ?_⟩
      have hLP : levi P R * uGL a 0 c * (levi P R)⁻¹ =
          uGL (actA 1 k P R a) 0 ((P : Matrix (Fin 1) (Fin 1) (ZMod 2)) * c *
            ((P⁻¹ : GL (Fin 1) (ZMod 2)) : Matrix (Fin 1) (Fin 1) (ZMod 2))) := by
        rw [levi_conj_uGL]
        simp only [actA, Matrix.mul_zero, Matrix.zero_mul]
      have hLP2 : levi P R * uGL 0 b c' * (levi P R)⁻¹ =
          uGL 0 (actB 1 k P R b) ((P : Matrix (Fin 1) (Fin 1) (ZMod 2)) * c' *
            ((P⁻¹ : GL (Fin 1) (ZMod 2)) : Matrix (Fin 1) (Fin 1) (ZMod 2))) := by
        rw [levi_conj_uGL]
        simp only [actB, Matrix.mul_zero, Matrix.zero_mul]
      calc α (uGL (actA 1 k P R a) 0 ((P : Matrix (Fin 1) (Fin 1) (ZMod 2)) * c *
              ((P⁻¹ : GL (Fin 1) (ZMod 2)) : Matrix (Fin 1) (Fin 1) (ZMod 2))))
          = α (levi P R * uGL a 0 c * (levi P R)⁻¹) := by rw [← hLP]
        _ = α (levi P R) * α (uGL a 0 c) * (α (levi P R))⁻¹ := by
              rw [map_mul, map_mul, map_inv]
        _ = (u' * levi P R) * uGL 0 b c' * (u' * levi P R)⁻¹ := by rw [hu'eq, hc]
        _ = u' * (levi P R * uGL 0 b c' * (levi P R)⁻¹) * u'⁻¹ := by group
        _ = u' * uGL 0 (actB 1 k P R b) ((P : Matrix (Fin 1) (Fin 1) (ZMod 2)) * c' *
              ((P⁻¹ : GL (Fin 1) (ZMod 2)) : Matrix (Fin 1) (Fin 1) (ZMod 2))) * u'⁻¹ := by
              rw [hLP2]
        _ = uGL 0 (actB 1 k P R b) c₂ := hc₂
    have hzpow : ∀ x : GL (BlkIdx 1 k) (ZMod 2),
        x ∈ Subgroup.zpowers (jGL 1 k) → α x ∈ Subgroup.zpowers (jGL 1 k) := by
      intro x hx
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← hn, map_zpow, hJ]
      exact Subgroup.zpow_mem_zpowers _ n
    have hA' : ∀ a, (a, (0 : Matrix (Fin k) (Fin 1) (ZMod 2))) ∈ W → a = 0 := by
      rintro a ⟨c, c', hc⟩
      have hz : α (uGL a 0 c) ∈ zSub 1 k := ⟨c', hc⟩
      rw [zSub_eq_zpowers] at hz
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hJ' : α.symm (jGL 1 k) = jGL 1 k :=
        α.injective (by rw [α.apply_symm_apply, hJ])
      have hu : uGL a 0 c ∈ zSub 1 k := by
        rw [zSub_eq_zpowers, Subgroup.mem_zpowers_iff]
        refine ⟨n, ?_⟩
        have h2 : α.symm ((jGL 1 k) ^ n) = uGL a 0 c := by
          rw [hn, α.symm_apply_apply]
        rwa [map_zpow, hJ'] at h2
      obtain ⟨c₀, hc₀⟩ := hu
      exact (uGL_injective hc₀).1
    have hB' : ∀ b, ((0 : Matrix (Fin 1) (Fin k) (ZMod 2)), b) ∈ W → b = 0 := by
      rintro b ⟨c, c', hc⟩
      have hz0 : uGL 0 0 c ∈ Subgroup.zpowers (jGL 1 k) := by
        rw [← zSub_eq_zpowers]
        exact ⟨c, rfl⟩
      have hz : α (uGL 0 0 c) ∈ zSub 1 k := by
        rw [zSub_eq_zpowers]
        exact hzpow _ hz0
      rw [hc] at hz
      obtain ⟨c₀, hc₀⟩ := hz
      exact (uGL_injective hc₀).2.1
    have hWbot : W = ⊥ := eq_bot_of_actA_actB 1 k (Or.inr hk) W hW hA' hB'
    have hk0 : 0 < k := by omega
    let i0 : Fin k := ⟨0, hk0⟩
    have ha0 : (Matrix.single (0 : Fin 1) i0 (1 : ZMod 2) :
        Matrix (Fin 1) (Fin k) (ZMod 2)) ≠ 0 := by
      intro h
      have h1 : (Matrix.single (0 : Fin 1) i0 (1 : ZMod 2) :
          Matrix (Fin 1) (Fin k) (ZMod 2)) 0 i0 =
          (0 : Matrix (Fin 1) (Fin k) (ZMod 2)) 0 i0 := by rw [h]
      rw [Matrix.single_apply_same, Matrix.zero_apply] at h1
      exact (by decide : (1 : ZMod 2) ≠ 0) h1
    obtain ⟨b, c', hb⟩ :=
      huOne_uTwo (uGL (Matrix.single 0 i0 1) 0 0) ⟨Matrix.single 0 i0 1, 0, rfl⟩
    have hmemW : ((Matrix.single (0 : Fin 1) i0 (1 : ZMod 2) :
        Matrix (Fin 1) (Fin k) (ZMod 2)), b) ∈ W := ⟨0, c', hb⟩
    rw [hWbot] at hmemW
    refine ha0 ?_
    have hzero : ((Matrix.single (0 : Fin 1) i0 (1 : ZMod 2) :
        Matrix (Fin 1) (Fin k) (ZMod 2)), b) = 0 := AddSubgroup.mem_bot.mp hmemW
    simpa using congrArg Prod.fst hzero

theorem isConj_map_of_mulAut {k : ℕ} (hk : 1 ≤ k) (α : MulAut (GL (BlkIdx 1 k) (ZMod 2)))
    {g : GL (BlkIdx 1 k) (ZMod 2)} (hg : IsConj (jGL 1 k) g) : IsConj (jGL 1 k) (α g) := by
  obtain ⟨A, hA | hA⟩ := exists_eq_conj_or_conj_inverseTranspose hk α
  · exact hg.trans (isConj_iff.mpr ⟨A, (hA g).symm⟩)
  · have hJα : IsConj (jGL 1 k) (α (jGL 1 k)) := by
      have hδ : IsConj (jGL 1 k) (Matrix.GeneralLinearGroup.inverseTranspose (jGL 1 k)) := by
        refine IsConj.symm (isConj_iff.mpr ⟨antiDiag k, ?_⟩)
        rw [← caRAut_sigmaStd_apply k (jGL 1 k)]
        exact sigmaStd_jGL k
      exact hδ.trans (isConj_iff.mpr ⟨A, (hA (jGL 1 k)).symm⟩)
    obtain ⟨x, hx⟩ := isConj_iff.mp hg
    refine hJα.trans (isConj_iff.mpr ⟨α x, ?_⟩)
    rw [← hx, map_mul, map_mul, map_inv]

end CFSG.StandardType.FF81.CentA

end
