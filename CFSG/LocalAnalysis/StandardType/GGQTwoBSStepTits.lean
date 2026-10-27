module

public import CFSG.LocalAnalysis.StandardType.GGQTwoBSDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoBSStab
import CFSG.LocalAnalysis.StandardType.GGQTwoBSGraph
import CFSG.LocalAnalysis.StandardType.GGQTwoBSGen
import CFSG.ClassicalInvolution.Phan.Frames.BlockStab
import CFSG.Monster.B.Recog.GenericTits
import CFSG.ClassicalInvolution.Phan.Frames.Action

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.ClassicalInvolution.Phan

open scoped Pointwise

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private def bshV (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ) :
    NormOneVec K (c + 3) :=
  NormOneVec.single (Fin.last (c + 2))

private def bshW (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ) :
    NormOneVec K (c + 3) :=
  NormOneVec.single ⟨c + 1, by omega⟩

private def bshU (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ) :
    NormOneVec K (c + 3) :=
  NormOneVec.single ⟨c, by omega⟩

private noncomputable def bshXv (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ) :
    Subgroup (Su K 2 1 (c + 3)) :=
  (blockEmb K 2 1 (c + 3) (c + 2) 0 (by omega)).range

private def bshXePred (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ)
    (g : Su K 2 1 (c + 3)) : Prop :=
  (g • bshV K c = bshV K c ∧ g • bshW K c = bshW K c) ∨
    (g • bshV K c = bshW K c ∧ g • bshW K c = bshV K c)

private theorem bshXePred_one (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ) :
    bshXePred K c 1 :=
  Or.inl ⟨one_smul _ _, one_smul _ _⟩

private theorem bshXePred_mul (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ)
    {g h : Su K 2 1 (c + 3)} (hg : bshXePred K c g) (hh : bshXePred K c h) :
    bshXePred K c (g * h) := by
  rcases hg with ⟨gv, gw⟩ | ⟨gv, gw⟩ <;> rcases hh with ⟨hv, hw⟩ | ⟨hv, hw⟩
  · exact Or.inl ⟨by rw [mul_smul, hv, gv], by rw [mul_smul, hw, gw]⟩
  · exact Or.inr ⟨by rw [mul_smul, hv, gw], by rw [mul_smul, hw, gv]⟩
  · exact Or.inr ⟨by rw [mul_smul, hv, gv], by rw [mul_smul, hw, gw]⟩
  · exact Or.inl ⟨by rw [mul_smul, hv, gw], by rw [mul_smul, hw, gv]⟩

private theorem bshXePred_inv (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ)
    {g : Su K 2 1 (c + 3)} (hg : bshXePred K c g) : bshXePred K c g⁻¹ := by
  rcases hg with ⟨gv, gw⟩ | ⟨gv, gw⟩
  · exact Or.inl ⟨by rw [inv_smul_eq_iff]; exact gv.symm,
      by rw [inv_smul_eq_iff]; exact gw.symm⟩
  · exact Or.inr ⟨by rw [inv_smul_eq_iff]; exact gw.symm,
      by rw [inv_smul_eq_iff]; exact gv.symm⟩

private noncomputable def bshXe (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ) :
    Subgroup (Su K 2 1 (c + 3)) where
  carrier := {g | bshXePred K c g}
  one_mem' := bshXePred_one K c
  mul_mem' := fun hg hh => bshXePred_mul K c hg hh
  inv_mem' := fun hg => bshXePred_inv K c hg

private noncomputable def bshXt (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ) :
    Subgroup (Su K 2 1 (c + 3)) :=
  (blockProd K c 3 (c + 3) rfl).range ⊓
    MulAction.stabilizer (Su K 2 1 (c + 3))
      ({bshU K c, bshV K c, bshW K c} : Set (NormOneVec K (c + 3)))

private noncomputable def bshTau (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ) :
    Su K 2 1 (c + 3) :=
  swapAt K (c + 3) (c + 1) (by omega)

private noncomputable def bshRho (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ) :
    Su K 2 1 (c + 3) :=
  bshTau K c * swapAt K (c + 3) c (by omega)

private theorem bsh_smul_single_eq {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    {g : Su K 2 1 m} {i j : Fin m}
    (h : g • (NormOneVec.single i : NormOneVec K m) =
      (NormOneVec.single j : NormOneVec K m)) :
    g • (Pi.single i 1 : Fin m → K) = Pi.single j 1 := by
  simpa only [NormOneVec.val_smul, NormOneVec.val_single] using congrArg NormOneVec.val h

private theorem bsh_ofInjective_symm_apply {M N : Type*} [Group M] [Group N] {f : M →* N}
    (hf : Function.Injective f) (x : M) :
    (MonoidHom.ofInjective hf).symm ⟨f x, Set.mem_range_self x⟩ = x := by
  rw [MulEquiv.symm_apply_eq]
  apply Subtype.ext
  rw [MonoidHom.ofInjective_apply]

private theorem bsh_hXv (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ) :
    ∀ g : Su K 2 1 (c + 3), g ∈ bshXv K c ↔ g • bshV K c = bshV K c := by
  intro g
  simp only [bshXv, bshV]
  rw [mem_range_blockEmb_iff (by omega)]
  constructor
  · intro h
    apply NormOneVec.ext
    simpa only [NormOneVec.val_smul, NormOneVec.val_single] using
      h (Fin.last (c + 2)) (by simp [Fin.last])
  · intro h l hl
    have hlt := l.isLt
    have hl2 : ¬ l.val < 0 + (c + 2) := fun hlt' => hl ⟨Nat.zero_le _, hlt'⟩
    have hlv : l.val = c + 2 := by omega
    have hl' : l = Fin.last (c + 2) := by
      apply Fin.ext
      rw [Fin.val_last]
      exact hlv
    rw [hl']
    exact bsh_smul_single_eq h

private theorem bsh_hXe (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ)
    (g : Su K 2 1 (c + 3)) : g ∈ bshXe K c ↔ bshXePred K c g :=
  Iff.rfl

private theorem bshXe_le (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ) :
    bshXe K c ≤ (blockProd K (c + 1) 2 (c + 3) (by omega)).range := by
  rintro g (⟨gv, gw⟩ | ⟨gv, gw⟩)
  · exact mem_range_blockProd_of_smul_pair g (Or.inl ⟨bsh_smul_single_eq gv,
      bsh_smul_single_eq gw⟩)
  · exact mem_range_blockProd_of_smul_pair g (Or.inr ⟨bsh_smul_single_eq gv,
      bsh_smul_single_eq gw⟩)

private theorem bsh_hXt (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ) :
    ∀ g ∈ bshXt K c, g • bshV K c = bshV K c ∨ g • bshV K c = bshW K c ∨
      g • bshV K c = bshU K c := by
  intro g hg
  obtain ⟨-, hstab⟩ := Subgroup.mem_inf.mp hg
  have hv : g • bshV K c ∈
      ({bshU K c, bshV K c, bshW K c} : Set (NormOneVec K (c + 3))) :=
    (MulAction.mem_stabilizer_set.mp hstab (bshV K c)).mpr (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with h | h | h
  · exact Or.inr (Or.inr h)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

private theorem bsh_tau_smul_v (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ) :
    bshTau K c • bshV K c = bshW K c := by
  apply NormOneVec.ext
  rw [NormOneVec.val_smul]
  simp only [bshTau, bshV, bshW, NormOneVec.val_single]
  exact swapAt_smul_single_right (K := K) (m := c + 3) (a := c + 1) (by omega)

private theorem bsh_tau_smul_w (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ) :
    bshTau K c • bshW K c = bshV K c := by
  apply NormOneVec.ext
  rw [NormOneVec.val_smul]
  simp only [bshTau, bshV, bshW, NormOneVec.val_single]
  exact swapAt_smul_single_left (K := K) (m := c + 3) (a := c + 1) (by omega)

private theorem bsh_tau_smul_u (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ) :
    bshTau K c • bshU K c = bshU K c := by
  apply NormOneVec.ext
  rw [NormOneVec.val_smul]
  simp only [bshTau, bshU, NormOneVec.val_single]
  exact swapAt_smul_single_of_ne (K := K) (m := c + 3) (a := c + 1) (by omega)
    (l := ⟨c, by omega⟩) (by dsimp only; omega)
      (by dsimp only; omega)

private theorem bsh_s_smul_u (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ) :
    swapAt K (c + 3) c (by omega) • bshU K c = bshW K c := by
  apply NormOneVec.ext
  rw [NormOneVec.val_smul]
  simp only [bshU, bshW, NormOneVec.val_single]
  exact swapAt_smul_single_left (K := K) (m := c + 3) (a := c) (by omega)

private theorem bsh_s_smul_w (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ) :
    swapAt K (c + 3) c (by omega) • bshW K c = bshU K c := by
  apply NormOneVec.ext
  rw [NormOneVec.val_smul]
  simp only [bshU, bshW, NormOneVec.val_single]
  exact swapAt_smul_single_right (K := K) (m := c + 3) (a := c) (by omega)

private theorem bsh_s_smul_v (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ) :
    swapAt K (c + 3) c (by omega) • bshV K c = bshV K c := by
  apply NormOneVec.ext
  rw [NormOneVec.val_smul]
  simp only [bshV, NormOneVec.val_single]
  exact swapAt_smul_single_of_ne (K := K) (m := c + 3) (a := c) (by omega)
    (l := Fin.last (c + 2)) (by simp only [Fin.val_last]; omega)
      (by simp only [Fin.val_last]; omega)

private theorem bsh_rho_smul_v (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ) :
    bshRho K c • bshV K c = bshW K c := by
  rw [bshRho, mul_smul, bsh_s_smul_v, bsh_tau_smul_v]

private theorem bsh_rho_smul_w (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ) :
    bshRho K c • bshW K c = bshU K c := by
  rw [bshRho, mul_smul, bsh_s_smul_w, bsh_tau_smul_u]

private theorem bsh_rho_smul_u (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ) :
    bshRho K c • bshU K c = bshV K c := by
  rw [bshRho, mul_smul, bsh_s_smul_u, bsh_tau_smul_w]

private theorem bsh_tau_mem_prod (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ) :
    bshTau K c ∈ (blockProd K c 3 (c + 3) rfl).range := by
  refine ⟨(1, blockEmb K 2 1 3 2 1 (by norm_num) (rotSU (unitaryInvolution K 2 1))), ?_⟩
  rw [blockProd_apply, map_one, one_mul, blockEmb_comp_apply]
  rfl

private theorem bsh_s_mem_prod (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ) :
    swapAt K (c + 3) c (by omega) ∈ (blockProd K c 3 (c + 3) rfl).range := by
  refine ⟨(1, blockEmb K 2 1 3 2 0 (by norm_num) (rotSU (unitaryInvolution K 2 1))), ?_⟩
  rw [blockProd_apply, map_one, one_mul, blockEmb_comp_apply]
  rfl

private theorem bsh_rho_mem_prod (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ) :
    bshRho K c ∈ (blockProd K c 3 (c + 3) rfl).range :=
  Subgroup.mul_mem _ (bsh_tau_mem_prod K c) (bsh_s_mem_prod K c)

private theorem bsh_tau_stab (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ) :
    bshTau K c • ({bshU K c, bshV K c, bshW K c} : Set (NormOneVec K (c + 3))) =
      {bshU K c, bshV K c, bshW K c} := by
  simp only [Set.smul_set_insert, Set.smul_set_singleton, bsh_tau_smul_u, bsh_tau_smul_v,
    bsh_tau_smul_w]
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem bsh_rho_stab (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ) :
    bshRho K c • ({bshU K c, bshV K c, bshW K c} : Set (NormOneVec K (c + 3))) =
      {bshU K c, bshV K c, bshW K c} := by
  simp only [Set.smul_set_insert, Set.smul_set_singleton, bsh_rho_smul_u, bsh_rho_smul_v,
    bsh_rho_smul_w]
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem bsh_tau_mem_Xt (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ) :
    bshTau K c ∈ bshXt K c := by
  refine Subgroup.mem_inf.mpr ⟨bsh_tau_mem_prod K c, ?_⟩
  rw [MulAction.mem_stabilizer_iff]
  exact bsh_tau_stab K c

private theorem bsh_rho_mem_Xt (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ) :
    bshRho K c ∈ bshXt K c := by
  refine Subgroup.mem_inf.mpr ⟨bsh_rho_mem_prod K c, ?_⟩
  rw [MulAction.mem_stabilizer_iff]
  exact bsh_rho_stab K c

private theorem bsh_exists_tau (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ) :
    ∃ g ∈ bshXt K c, g • bshV K c = bshW K c ∧ g • bshW K c = bshV K c :=
  ⟨bshTau K c, bsh_tau_mem_Xt K c, bsh_tau_smul_v K c, bsh_tau_smul_w K c⟩

private theorem bsh_exists_rho (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ) :
    ∃ g ∈ bshXt K c, g • bshV K c = bshW K c ∧ g • bshW K c = bshU K c ∧
      g • bshU K c = bshV K c :=
  ⟨bshRho K c, bsh_rho_mem_Xt K c, bsh_rho_smul_v K c, bsh_rho_smul_w K c,
    bsh_rho_smul_u K c⟩

private noncomputable def bshPhiV (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ)
    {Y : Type} [Group Y] (ψ₀ : Su K 2 1 (c + 2) →* Y) : bshXv K c →* Y :=
  ψ₀.comp (MonoidHom.ofInjective
    (blockEmb_injective (K := K) (m := c + 3) (k := c + 2) (i := 0) (by omega))).symm.toMonoidHom

private noncomputable def bshPhiE (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ)
    {Y : Type} [Group Y] (F : QTwoPhanFamily K Y (c + 2))
    (ψ₀ : Su K 2 1 (c + 2) →* Y)
    (hcomm : ∀ (A : Su K 2 1 (c + 1)) (B : Su K 2 1 2),
      Commute (ψ₀ (blockEmb K 2 1 (c + 2) (c + 1) 0 (by omega) A))
        (F.ι (Fin.last (c + 1)) B)) : bshXe K c →* Y :=
  (MonoidHom.noncommCoprod (ψ₀.comp (blockEmb K 2 1 (c + 2) (c + 1) 0 (by omega)))
    (F.ι (Fin.last (c + 1))) hcomm).comp
    ((MonoidHom.ofInjective (blockProd_injective (K := K) (a := c + 1) (b := 2)
      (m := c + 3) (by omega))).symm.toMonoidHom.comp (Subgroup.inclusion (bshXe_le K c)))

private noncomputable def bshPhiT (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ)
    {Y : Type} [Group Y] (F : QTwoPhanFamily K Y (c + 2))
    (ψ₀ : Su K 2 1 (c + 2) →* Y)
    (hcomm : ∀ (A : Su K 2 1 c) (B : Su K 2 1 3),
      Commute (ψ₀ (blockEmb K 2 1 (c + 2) c 0 (by omega) A)) (F.θ ⟨c, by omega⟩ B)) :
    bshXt K c →* Y :=
  (MonoidHom.noncommCoprod (ψ₀.comp (blockEmb K 2 1 (c + 2) c 0 (by omega)))
    (F.θ ⟨c, by omega⟩) hcomm).comp
    ((MonoidHom.ofInjective (blockProd_injective (K := K) (a := c) (b := 3)
      (m := c + 3) rfl)).symm.toMonoidHom.comp
      (Subgroup.inclusion (inf_le_left : bshXt K c ≤
        (blockProd K c 3 (c + 3) rfl).range)))

private theorem bshPhiV_apply (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ)
    {Y : Type} [Group Y] (ψ₀ : Su K 2 1 (c + 2) →* Y) (x : Su K 2 1 (c + 2))
    (hx : blockEmb K 2 1 (c + 3) (c + 2) 0 (by omega) x ∈ bshXv K c) :
    bshPhiV K c ψ₀ ⟨blockEmb K 2 1 (c + 3) (c + 2) 0 (by omega) x, hx⟩ = ψ₀ x := by
  change ψ₀ ((MonoidHom.ofInjective
    (blockEmb_injective (K := K) (m := c + 3) (k := c + 2) (i := 0) (by omega))).symm
      ⟨blockEmb K 2 1 (c + 3) (c + 2) 0 (by omega) x, hx⟩) = ψ₀ x
  rw [bsh_ofInjective_symm_apply]

private theorem bshPhiE_apply (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ)
    {Y : Type} [Group Y] (F : QTwoPhanFamily K Y (c + 2))
    (ψ₀ : Su K 2 1 (c + 2) →* Y)
    (hcomm : ∀ (A : Su K 2 1 (c + 1)) (B : Su K 2 1 2),
      Commute (ψ₀ (blockEmb K 2 1 (c + 2) (c + 1) 0 (by omega) A))
        (F.ι (Fin.last (c + 1)) B))
    (A : Su K 2 1 (c + 1)) (B : Su K 2 1 2)
    (hmem : blockProd K (c + 1) 2 (c + 3) (by omega) (A, B) ∈ bshXe K c) :
    bshPhiE K c F ψ₀ hcomm
        ⟨blockProd K (c + 1) 2 (c + 3) (by omega) (A, B), hmem⟩ =
      ψ₀ (blockEmb K 2 1 (c + 2) (c + 1) 0 (by omega) A) *
        F.ι (Fin.last (c + 1)) B := by
  change (MonoidHom.noncommCoprod (ψ₀.comp (blockEmb K 2 1 (c + 2) (c + 1) 0 (by omega)))
      (F.ι (Fin.last (c + 1))) hcomm)
    ((MonoidHom.ofInjective (blockProd_injective (K := K) (a := c + 1) (b := 2)
      (m := c + 3) (by omega))).symm
      ((Subgroup.inclusion (bshXe_le K c))
        ⟨blockProd K (c + 1) 2 (c + 3) (by omega) (A, B), hmem⟩)) =
    ψ₀ (blockEmb K 2 1 (c + 2) (c + 1) 0 (by omega) A) *
      F.ι (Fin.last (c + 1)) B
  have hinc : (Subgroup.inclusion (bshXe_le K c))
      ⟨blockProd K (c + 1) 2 (c + 3) (by omega) (A, B), hmem⟩ =
      ⟨blockProd K (c + 1) 2 (c + 3) (by omega) (A, B), bshXe_le K c hmem⟩ := rfl
  rw [hinc, bsh_ofInjective_symm_apply, MonoidHom.noncommCoprod_apply, MonoidHom.comp_apply]

private theorem bshPhiT_apply (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ)
    {Y : Type} [Group Y] (F : QTwoPhanFamily K Y (c + 2))
    (ψ₀ : Su K 2 1 (c + 2) →* Y)
    (hcomm : ∀ (A : Su K 2 1 c) (B : Su K 2 1 3),
      Commute (ψ₀ (blockEmb K 2 1 (c + 2) c 0 (by omega) A)) (F.θ ⟨c, by omega⟩ B))
    (A : Su K 2 1 c) (B : Su K 2 1 3)
    (hmem : blockProd K c 3 (c + 3) rfl (A, B) ∈ bshXt K c) :
    bshPhiT K c F ψ₀ hcomm ⟨blockProd K c 3 (c + 3) rfl (A, B), hmem⟩ =
      ψ₀ (blockEmb K 2 1 (c + 2) c 0 (by omega) A) * F.θ ⟨c, by omega⟩ B := by
  change (MonoidHom.noncommCoprod (ψ₀.comp (blockEmb K 2 1 (c + 2) c 0 (by omega)))
      (F.θ ⟨c, by omega⟩) hcomm)
    ((MonoidHom.ofInjective (blockProd_injective (K := K) (a := c) (b := 3)
      (m := c + 3) rfl)).symm
      ((Subgroup.inclusion (inf_le_left : bshXt K c ≤
        (blockProd K c 3 (c + 3) rfl).range))
        ⟨blockProd K c 3 (c + 3) rfl (A, B), hmem⟩)) =
    ψ₀ (blockEmb K 2 1 (c + 2) c 0 (by omega) A) * F.θ ⟨c, by omega⟩ B
  have hinc : (Subgroup.inclusion (inf_le_left : bshXt K c ≤
      (blockProd K c 3 (c + 3) rfl).range))
      ⟨blockProd K c 3 (c + 3) rfl (A, B), hmem⟩ =
      ⟨blockProd K c 3 (c + 3) rfl (A, B),
        (inf_le_left : bshXt K c ≤ (blockProd K c 3 (c + 3) rfl).range) hmem⟩ := rfl
  rw [hinc, bsh_ofInjective_symm_apply, MonoidHom.noncommCoprod_apply, MonoidHom.comp_apply]

private theorem bsh_hcommE (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 4) (c : ℕ) (hc : 4 ≤ c) {Y : Type} [Group Y]
    (F : QTwoPhanFamily K Y (c + 2)) (ψ₀ : Su K 2 1 (c + 2) →* Y)
    (hθ : ∀ (i : Fin (c + 1)) (h : (i : ℕ) + 1 < c + 1),
      ψ₀.comp (blockEmb3 K 2 1 (c + 1) i h) = F.θ i.castSucc) :
    ∀ (A : Su K 2 1 (c + 1)) (B : Su K 2 1 2),
      Commute (ψ₀ (blockEmb K 2 1 (c + 2) (c + 1) 0 (by omega) A))
        (F.ι (Fin.last (c + 1)) B) := by
  intro A B
  have hθ' : ∀ (i : ℕ) (hi : i + 1 < c + 1) (y : Su K 2 1 3),
      ψ₀ (blockEmb K 2 1 (c + 2) 3 i (by omega) y) =
        F.θ (⟨i, by omega⟩ : Fin (c + 2)) y := by
    intro i hi y
    have hcast : (⟨i, by omega⟩ : Fin (c + 1)).castSucc = (⟨i, by omega⟩ : Fin (c + 2)) :=
      rfl
    have := DFunLike.congr_fun (hθ ⟨i, by omega⟩ (by simpa using hi)) y
    rw [hcast] at this
    simpa only [MonoidHom.comp_apply, blockEmb3] using this
  have hgen : (⨆ (i : ℕ) (h : i + 3 ≤ c + 1),
      (blockEmb K 2 1 (c + 1) 3 i h).range) = ⊤ :=
    iSup_range_blockEmb_three hK (by omega)
  have hle : (⨆ (i : ℕ) (h : i + 3 ≤ c + 1),
      (blockEmb K 2 1 (c + 1) 3 i h).range) ≤
      (Subgroup.centralizer (F.ι (Fin.last (c + 1))).range).comap
        (ψ₀.comp (blockEmb K 2 1 (c + 2) (c + 1) 0 (by omega))) := by
    refine iSup_le fun i => iSup_le fun h => ?_
    rintro x ⟨y, rfl⟩
    rw [Subgroup.mem_comap, MonoidHom.comp_apply, blockEmb_comp_apply,
      Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨b, rfl⟩ := Set.mem_range.mp hz
    have hθi : ψ₀ (blockEmb K 2 1 (c + 2) 3 (0 + i) (by omega) y) =
        F.θ (⟨i, by omega⟩ : Fin (c + 2)) y := by
      simpa only [Nat.zero_add] using hθ' i (by omega) y
    rw [hθi]
    exact F.farNodeEdge (Fin.last (c + 1)) ⟨i, by omega⟩
      (by dsimp only; omega)
      (by
        change (c + 1) + 1 < i ∨ i + 2 < c + 1
        omega) b y
  have htop : (⊤ : Subgroup (Su K 2 1 (c + 1))) ≤
      (Subgroup.centralizer (F.ι (Fin.last (c + 1))).range).comap
        (ψ₀.comp (blockEmb K 2 1 (c + 2) (c + 1) 0 (by omega))) := by
    rw [← hgen]
    exact hle
  exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp
    (htop (Subgroup.mem_top A)))) (F.ι (Fin.last (c + 1)) B) ⟨B, rfl⟩).symm

private theorem bsh_hcommT (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 4) (c : ℕ) (hc : 4 ≤ c) {Y : Type} [Group Y]
    (F : QTwoPhanFamily K Y (c + 2)) (ψ₀ : Su K 2 1 (c + 2) →* Y)
    (hθ : ∀ (i : Fin (c + 1)) (h : (i : ℕ) + 1 < c + 1),
      ψ₀.comp (blockEmb3 K 2 1 (c + 1) i h) = F.θ i.castSucc) :
    ∀ (A : Su K 2 1 c) (B : Su K 2 1 3),
      Commute (ψ₀ (blockEmb K 2 1 (c + 2) c 0 (by omega) A))
        (F.θ ⟨c, by omega⟩ B) := by
  intro A B
  have hθ' : ∀ (i : ℕ) (hi : i + 1 < c + 1) (y : Su K 2 1 3),
      ψ₀ (blockEmb K 2 1 (c + 2) 3 i (by omega) y) =
        F.θ (⟨i, by omega⟩ : Fin (c + 2)) y := by
    intro i hi y
    have hcast : (⟨i, by omega⟩ : Fin (c + 1)).castSucc = (⟨i, by omega⟩ : Fin (c + 2)) :=
      rfl
    have := DFunLike.congr_fun (hθ ⟨i, by omega⟩ (by simpa using hi)) y
    rw [hcast] at this
    simpa only [MonoidHom.comp_apply, blockEmb3] using this
  have hgen : (⨆ (i : ℕ) (h : i + 3 ≤ c),
      (blockEmb K 2 1 c 3 i h).range) = ⊤ :=
    iSup_range_blockEmb_three hK (by omega)
  have hle : (⨆ (i : ℕ) (h : i + 3 ≤ c),
      (blockEmb K 2 1 c 3 i h).range) ≤
      (Subgroup.centralizer (F.θ ⟨c, by omega⟩).range).comap
        (ψ₀.comp (blockEmb K 2 1 (c + 2) c 0 (by omega))) := by
    refine iSup_le fun i => iSup_le fun h => ?_
    rintro x ⟨y, rfl⟩
    rw [Subgroup.mem_comap, MonoidHom.comp_apply, blockEmb_comp_apply,
      Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨b, rfl⟩ := Set.mem_range.mp hz
    have hθi : ψ₀ (blockEmb K 2 1 (c + 2) 3 (0 + i) (by omega) y) =
        F.θ (⟨i, by omega⟩ : Fin (c + 2)) y := by
      simpa only [Nat.zero_add] using hθ' i (by omega) y
    rw [hθi]
    exact (F.farEdgeEdge (⟨i, by omega⟩ : Fin (c + 2)) ⟨c, by omega⟩
      (by dsimp only; omega)
      (by dsimp only; omega) y b).symm
  have htop : (⊤ : Subgroup (Su K 2 1 c)) ≤
      (Subgroup.centralizer (F.θ ⟨c, by omega⟩).range).comap
        (ψ₀.comp (blockEmb K 2 1 (c + 2) c 0 (by omega))) := by
    rw [← hgen]
    exact hle
  exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp
    (htop (Subgroup.mem_top A)))) (F.θ ⟨c, by omega⟩ B) ⟨B, rfl⟩).symm

private theorem bshV_ne_W (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ) :
    bshV K c ≠ bshW K c := by
  intro h
  have hval := congrArg (fun x : NormOneVec K (c + 3) => x.val (Fin.last (c + 2))) h
  simp only [bshV, bshW, NormOneVec.val_single] at hval
  have hne : (Fin.last (c + 2) : Fin (c + 3)) ≠ ⟨c + 1, by omega⟩ := by
    intro hEq
    have := congrArg Fin.val hEq
    change c + 2 = c + 1 at this
    omega
  rw [Pi.single_eq_same, Pi.single_eq_of_ne hne] at hval
  exact one_ne_zero hval

private theorem bsh_hve (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ)
    {Y : Type} [Group Y] (F : QTwoPhanFamily K Y (c + 2))
    (ψ₀ : Su K 2 1 (c + 2) →* Y)
    (hcomm : ∀ (A : Su K 2 1 (c + 1)) (B : Su K 2 1 2),
      Commute (ψ₀ (blockEmb K 2 1 (c + 2) (c + 1) 0 (by omega) A))
        (F.ι (Fin.last (c + 1)) B)) :
    ∀ a (ha : a ∈ bshXv K c) (hb : a ∈ bshXe K c),
      bshPhiV K c ψ₀ ⟨a, ha⟩ = bshPhiE K c F ψ₀ hcomm ⟨a, hb⟩ := by
  intro a ha hb
  have hav : a • bshV K c = bshV K c := (bsh_hXv K c a).mp ha
  have haw : a • bshW K c = bshW K c := by
    rcases (bsh_hXe K c a).mp hb with h | h
    · exact h.2
    · exact absurd (hav.symm.trans h.1) (bshV_ne_W K c)
  have hmem : a ∈ (blockEmb K 2 1 (c + 3) (c + 1) 0 (by omega)).range := by
    rw [mem_range_blockEmb_iff (by omega)]
    intro l hl
    have hlt := l.isLt
    have hl2 : ¬ l.val < 0 + (c + 1) := fun hlt' => hl ⟨Nat.zero_le _, hlt'⟩
    have hl' : l.val = c + 1 ∨ l.val = c + 2 := by omega
    rcases hl' with h | h
    · have hlw : l = (⟨c + 1, by omega⟩ : Fin (c + 3)) := by
        apply Fin.ext
        simpa only [Fin.val_mk] using h
      rw [hlw]
      exact bsh_smul_single_eq haw
    · have hlv : l = Fin.last (c + 2) := by
        apply Fin.ext
        rw [Fin.val_last]
        exact h
      rw [hlv]
      exact bsh_smul_single_eq hav
  obtain ⟨b, rfl⟩ := Set.mem_range.mp hmem
  have ha1 : blockEmb K 2 1 (c + 3) (c + 1) 0 (by omega) b =
      blockEmb K 2 1 (c + 3) (c + 2) 0 (by omega)
        (blockEmb K 2 1 (c + 2) (c + 1) 0 (by omega) b) := by
    rw [blockEmb_comp_apply]
  have ha2 : blockEmb K 2 1 (c + 3) (c + 1) 0 (by omega) b =
      blockProd K (c + 1) 2 (c + 3) (by omega) (b, 1) := by
    rw [blockProd_apply, map_one, mul_one]
  have hL : bshPhiV K c ψ₀
      ⟨blockEmb K 2 1 (c + 3) (c + 1) 0 (by omega) b, ha⟩ =
      ψ₀ (blockEmb K 2 1 (c + 2) (c + 1) 0 (by omega) b) := by
    have hsub : (⟨blockEmb K 2 1 (c + 3) (c + 1) 0 (by omega) b, ha⟩ : bshXv K c) =
        ⟨blockEmb K 2 1 (c + 3) (c + 2) 0 (by omega)
          (blockEmb K 2 1 (c + 2) (c + 1) 0 (by omega) b), ⟨_, rfl⟩⟩ :=
      Subtype.ext ha1
    rw [hsub]
    exact bshPhiV_apply K c ψ₀ _ _
  have hR : bshPhiE K c F ψ₀ hcomm
      ⟨blockEmb K 2 1 (c + 3) (c + 1) 0 (by omega) b, hb⟩ =
      ψ₀ (blockEmb K 2 1 (c + 2) (c + 1) 0 (by omega) b) := by
    have hsub : (⟨blockEmb K 2 1 (c + 3) (c + 1) 0 (by omega) b, hb⟩ : bshXe K c) =
        ⟨blockProd K (c + 1) 2 (c + 3) (by omega) (b, 1), ha2 ▸ hb⟩ :=
      Subtype.ext ha2
    rw [hsub, bshPhiE_apply, map_one, mul_one]
  rw [hL, hR]

private theorem bsh_hvt (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ)
    {Y : Type} [Group Y] (F : QTwoPhanFamily K Y (c + 2))
    (ψ₀ : Su K 2 1 (c + 2) →* Y)
    (hcomm : ∀ (A : Su K 2 1 c) (B : Su K 2 1 3),
      Commute (ψ₀ (blockEmb K 2 1 (c + 2) c 0 (by omega) A)) (F.θ ⟨c, by omega⟩ B))
    (hι : ∀ i : Fin (c + 1),
      ψ₀.comp (blockEmb2 K 2 1 (c + 1) i) = F.ι i.castSucc) :
    ∀ a (ha : a ∈ bshXv K c) (hb : a ∈ bshXt K c),
      bshPhiV K c ψ₀ ⟨a, ha⟩ = bshPhiT K c F ψ₀ hcomm ⟨a, hb⟩ := by
  intro a ha hb
  obtain ⟨hbR, -⟩ := Subgroup.mem_inf.mp hb
  obtain ⟨⟨A, B⟩, rfl⟩ := Set.mem_range.mp hbR
  have hav : blockProd K c 3 (c + 3) rfl (A, B) • bshV K c = bshV K c :=
    (bsh_hXv K c _).mp ha
  have hfix : blockProd K c 3 (c + 3) rfl (A, B) •
      (Pi.single (Fin.last (c + 2)) 1 : Fin (c + 3) → K) =
        Pi.single (Fin.last (c + 2)) 1 := bsh_smul_single_eq hav
  obtain ⟨b, hbB⟩ := Set.mem_range.mp (mem_range_blockEmb_of_blockProd_smul_last hfix)
  have hιc : ∀ y : Su K 2 1 2,
      ψ₀ (blockEmb K 2 1 (c + 2) 2 c (by omega) y) =
        F.ι (⟨c, by omega⟩ : Fin (c + 2)) y := by
    intro y
    have hcast : (⟨c, by omega⟩ : Fin (c + 1)).castSucc = (⟨c, by omega⟩ : Fin (c + 2)) :=
      rfl
    have := DFunLike.congr_fun (hι ⟨c, by omega⟩) y
    rw [hcast] at this
    simpa only [MonoidHom.comp_apply, blockEmb2] using this
  have hleft : F.θ (⟨c, by omega⟩ : Fin (c + 2))
      (blockEmb K 2 1 3 2 0 (by norm_num) b) =
        F.ι (⟨c, by omega⟩ : Fin (c + 2)) b := by
    have := DFunLike.congr_fun (F.left ⟨c, by omega⟩
      (by dsimp only; omega)) b
    simpa only [MonoidHom.comp_apply, embSUid_two_eq_blockEmb] using this
  have ha_eq : blockProd K c 3 (c + 3) rfl (A, B) =
      blockEmb K 2 1 (c + 3) (c + 2) 0 (by omega)
        (blockEmb K 2 1 (c + 2) c 0 (by omega) A *
          blockEmb K 2 1 (c + 2) 2 c (by omega) b) := by
    rw [blockProd_apply, ← hbB, map_mul]
    simp only [blockEmb_comp_apply, Nat.zero_add, Nat.add_zero]
  have hsub : (⟨blockProd K c 3 (c + 3) rfl (A, B), ha⟩ : bshXv K c) =
      ⟨blockEmb K 2 1 (c + 3) (c + 2) 0 (by omega)
        (blockEmb K 2 1 (c + 2) c 0 (by omega) A *
          blockEmb K 2 1 (c + 2) 2 c (by omega) b), ⟨_, rfl⟩⟩ :=
    Subtype.ext ha_eq
  have hL : bshPhiV K c ψ₀ ⟨blockProd K c 3 (c + 3) rfl (A, B), ha⟩ =
      ψ₀ (blockEmb K 2 1 (c + 2) c 0 (by omega) A) *
        F.ι (⟨c, by omega⟩ : Fin (c + 2)) b := by
    rw [hsub]
    exact (bshPhiV_apply K c ψ₀ _ _).trans (by rw [map_mul, hιc])
  have hR : bshPhiT K c F ψ₀ hcomm ⟨blockProd K c 3 (c + 3) rfl (A, B), hb⟩ =
      ψ₀ (blockEmb K 2 1 (c + 2) c 0 (by omega) A) *
        F.ι (⟨c, by omega⟩ : Fin (c + 2)) b := by
    rw [bshPhiT_apply, ← hbB, hleft]
  rw [hL, hR]

private theorem bsh_het (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ)
    {Y : Type} [Group Y] (F : QTwoPhanFamily K Y (c + 2))
    (ψ₀ : Su K 2 1 (c + 2) →* Y)
    (hcommE : ∀ (A : Su K 2 1 (c + 1)) (B : Su K 2 1 2),
      Commute (ψ₀ (blockEmb K 2 1 (c + 2) (c + 1) 0 (by omega) A))
        (F.ι (Fin.last (c + 1)) B))
    (hcommT : ∀ (A : Su K 2 1 c) (B : Su K 2 1 3),
      Commute (ψ₀ (blockEmb K 2 1 (c + 2) c 0 (by omega) A)) (F.θ ⟨c, by omega⟩ B)) :
    ∀ a (ha : a ∈ bshXe K c) (hb : a ∈ bshXt K c),
      bshPhiE K c F ψ₀ hcommE ⟨a, ha⟩ = bshPhiT K c F ψ₀ hcommT ⟨a, hb⟩ := by
  intro a ha hb
  obtain ⟨hbR, -⟩ := Subgroup.mem_inf.mp hb
  obtain ⟨⟨A, B⟩, rfl⟩ := Set.mem_range.mp hbR
  have hp : (blockProd K c 3 (c + 3) rfl (A, B) •
        (Pi.single (Fin.last (c + 2)) 1 : Fin (c + 3) → K) =
          Pi.single (Fin.last (c + 2)) 1 ∧
      blockProd K c 3 (c + 3) rfl (A, B) •
        (Pi.single (⟨c + 1, by omega⟩ : Fin (c + 3)) 1 : Fin (c + 3) → K) =
          Pi.single (⟨c + 1, by omega⟩ : Fin (c + 3)) 1) ∨
      (blockProd K c 3 (c + 3) rfl (A, B) •
        (Pi.single (Fin.last (c + 2)) 1 : Fin (c + 3) → K) =
          Pi.single (⟨c + 1, by omega⟩ : Fin (c + 3)) 1 ∧
      blockProd K c 3 (c + 3) rfl (A, B) •
        (Pi.single (⟨c + 1, by omega⟩ : Fin (c + 3)) 1 : Fin (c + 3) → K) =
          Pi.single (Fin.last (c + 2)) 1) := by
    rcases (bsh_hXe K c _).mp ha with h | h
    · exact Or.inl ⟨bsh_smul_single_eq h.1, bsh_smul_single_eq h.2⟩
    · exact Or.inr ⟨bsh_smul_single_eq h.1, bsh_smul_single_eq h.2⟩
  obtain ⟨b, hbB⟩ := Set.mem_range.mp (mem_range_blockEmb_of_blockProd_smul_pair hp)
  have ha_eq : blockProd K c 3 (c + 3) rfl (A, B) =
      blockProd K (c + 1) 2 (c + 3) (by omega)
        (blockEmb K 2 1 (c + 1) c 0 (by omega) A, b) := by
    rw [blockProd_apply, blockProd_apply, ← hbB]
    simp only [blockEmb_comp_apply]
  have hright : F.θ (⟨c, by omega⟩ : Fin (c + 2))
      (blockEmb K 2 1 3 2 1 (by norm_num) b) = F.ι (Fin.last (c + 1)) b := by
    have := DFunLike.congr_fun (F.right ⟨c, by omega⟩
      (by dsimp only; omega)) b
    have hidx : (⟨c + 1, by omega⟩ : Fin (c + 2)) = Fin.last (c + 1) := rfl
    simpa only [MonoidHom.comp_apply, embSUid_zero_eq_blockEmb, Fin.val_castSucc,
      Fin.val_last, hidx] using this
  have hsub : (⟨blockProd K c 3 (c + 3) rfl (A, B), ha⟩ : bshXe K c) =
      ⟨blockProd K (c + 1) 2 (c + 3) (by omega)
        (blockEmb K 2 1 (c + 1) c 0 (by omega) A, b), ha_eq ▸ ha⟩ :=
    Subtype.ext ha_eq
  have hL : bshPhiE K c F ψ₀ hcommE ⟨blockProd K c 3 (c + 3) rfl (A, B), ha⟩ =
      ψ₀ (blockEmb K 2 1 (c + 2) c 0 (by omega) A) *
        F.ι (Fin.last (c + 1)) b := by
    rw [hsub]
    exact (bshPhiE_apply K c F ψ₀ hcommE _ _ _).trans (by rw [blockEmb_comp_apply])
  have hR : bshPhiT K c F ψ₀ hcommT ⟨blockProd K c 3 (c + 3) rfl (A, B), hb⟩ =
      ψ₀ (blockEmb K 2 1 (c + 2) c 0 (by omega) A) *
        F.ι (Fin.last (c + 1)) b := by
    rw [bshPhiT_apply, ← hbB, hright]
  rw [hL, hR]

private theorem bsh_hvw (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ) :
    (orthGraph K (c + 3)).Adj (bshV K c) (bshW K c) := by
  have h := orthGraph_adj_single (K := K) (m := c + 3)
    (i := Fin.last (c + 2)) (j := ⟨c + 1, by omega⟩) (by
      intro hEq
      exact bshV_ne_W K c (by rw [bshV, bshW, hEq]))
  simpa only [bshV, bshW] using h

private theorem bsh_hwu (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ) :
    (orthGraph K (c + 3)).Adj (bshW K c) (bshU K c) := by
  have h := orthGraph_adj_single (K := K) (m := c + 3)
    (i := ⟨c + 1, by omega⟩) (j := ⟨c, by omega⟩) (by
      intro hEq
      have hv := congrArg Fin.val hEq
      dsimp only at hv
      omega)
  simpa only [bshW, bshU] using h

private theorem bsh_huv (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ) :
    (orthGraph K (c + 3)).Adj (bshU K c) (bshV K c) := by
  have h := orthGraph_adj_single (K := K) (m := c + 3)
    (i := ⟨c, by omega⟩) (j := Fin.last (c + 2)) (by
      intro hEq
      have hv := congrArg Fin.val hEq
      change c = c + 2 at hv
      omega)
  simpa only [bshU, bshV] using h

private theorem bsh_comp_blockEmb (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ)
    {Y : Type} [Group Y] (ψ₀ : Su K 2 1 (c + 2) →* Y)
    (Φ : Su K 2 1 (c + 3) →* Y)
    (hΦv : ∀ a : bshXv K c, Φ a = bshPhiV K c ψ₀ a) :
    Φ.comp (blockEmb K 2 1 (c + 3) (c + 2) 0 (by omega)) = ψ₀ := by
  ext x
  have hmem : blockEmb K 2 1 (c + 3) (c + 2) 0 (by omega) x ∈ bshXv K c := ⟨x, rfl⟩
  change Φ (blockEmb K 2 1 (c + 3) (c + 2) 0 (by omega) x) = ψ₀ x
  rw [hΦv ⟨blockEmb K 2 1 (c + 3) (c + 2) 0 (by omega) x, hmem⟩]
  exact bshPhiV_apply K c ψ₀ x hmem

private theorem bsh_phi_tau (K : Type) [Field K] [Finite K] [CharP K 2] (c : ℕ)
    {Y : Type} [Group Y] (F : QTwoPhanFamily K Y (c + 2))
    (ψ₀ : Su K 2 1 (c + 2) →* Y)
    (hcomm : ∀ (A : Su K 2 1 (c + 1)) (B : Su K 2 1 2),
      Commute (ψ₀ (blockEmb K 2 1 (c + 2) (c + 1) 0 (by omega) A))
        (F.ι (Fin.last (c + 1)) B))
    (Φ : Su K 2 1 (c + 3) →* Y)
    (hΦe : ∀ a : bshXe K c, Φ a = bshPhiE K c F ψ₀ hcomm a) :
    Φ (bshTau K c) = F.ι (Fin.last (c + 1)) (rotSU (unitaryInvolution K 2 1)) := by
  have hτXe : bshTau K c ∈ bshXe K c :=
    (bsh_hXe K c _).mpr (Or.inr ⟨bsh_tau_smul_v K c, bsh_tau_smul_w K c⟩)
  have hτ_prod : bshTau K c = blockProd K (c + 1) 2 (c + 3) (by omega)
      (1, rotSU (unitaryInvolution K 2 1)) := by
    rw [blockProd_apply, map_one, one_mul]
    rfl
  have hsub : (⟨bshTau K c, hτXe⟩ : bshXe K c) =
      ⟨blockProd K (c + 1) 2 (c + 3) (by omega)
        (1, rotSU (unitaryInvolution K 2 1)), hτ_prod ▸ hτXe⟩ :=
    Subtype.ext hτ_prod
  calc Φ (bshTau K c)
      = bshPhiE K c F ψ₀ hcomm ⟨bshTau K c, hτXe⟩ := hΦe ⟨bshTau K c, hτXe⟩
    _ = bshPhiE K c F ψ₀ hcomm
          ⟨blockProd K (c + 1) 2 (c + 3) (by omega)
            (1, rotSU (unitaryInvolution K 2 1)), hτ_prod ▸ hτXe⟩ := by
        rw [hsub]
    _ = ψ₀ (blockEmb K 2 1 (c + 2) (c + 1) 0 (by omega) 1) *
          F.ι (Fin.last (c + 1)) (rotSU (unitaryInvolution K 2 1)) :=
        bshPhiE_apply K c F ψ₀ hcomm 1 (rotSU (unitaryInvolution K 2 1)) _
    _ = F.ι (Fin.last (c + 1)) (rotSU (unitaryInvolution K 2 1)) := by
        rw [map_one, map_one, one_mul]

theorem exists_hom_comp_blockEmb_eq (hK : Nat.card K = 4) {n : ℕ} (hn : 5 ≤ n) {Y : Type}
    [Group Y] (F : QTwoPhanFamily K Y (n + 1)) (ψ₀ : Su K 2 1 (n + 1) →* Y)
    (hι : ∀ i : Fin n, ψ₀.comp (blockEmb2 K 2 1 n i) = F.ι i.castSucc)
    (hθ : ∀ (i : Fin n) (h : (i : ℕ) + 1 < n), ψ₀.comp (blockEmb3 K 2 1 n i h) = F.θ i.castSucc) :
    ∃ Φ : Su K 2 1 (n + 1 + 1) →* Y,
      Φ.comp (blockEmb K 2 1 (n + 1 + 1) (n + 1) 0 (by omega)) = ψ₀ ∧
        Φ (swapAt K (n + 1 + 1) n (by omega)) =
          F.ι (Fin.last n) (rotSU (unitaryInvolution K 2 1)) := by
  obtain ⟨c, rfl⟩ : ∃ c, n = c + 1 := ⟨n - 1, by omega⟩
  have hc : 4 ≤ c := by omega
  have hcommE := bsh_hcommE K hK c hc F ψ₀ hθ
  have hcommT := bsh_hcommT K hK c hc F ψ₀ hθ
  obtain ⟨Φ, ⟨hΦv, hΦe, -⟩, -⟩ :=
    CFSG.Monster.B.Recog.tits_universal_completion_of_arcTransitive
      (G := orthGraph K (c + 3)) (X := Su K 2 1 (c + 3))
      (orthGraph_adj_smul (K := K) (m := c + 3))
      (orthGraph_preconnected hK (m := c + 3) (by omega))
      (orthGraph_triangulable hK (m := c + 3) (by omega))
      (fun a b c' d hab hcd => orthGraph_arc hK (m := c + 3) (by omega) hab hcd)
      (bsh_hvw K c) (bshXv K c) (bshXe K c) (bsh_hXv K c) (bsh_hXe K c)
      (fun _ : Unit => bshU K c) (fun _ : Unit => bshXt K c)
      (fun _ => bsh_hXt K c) (fun _ => bsh_exists_tau K c)
      (fun _ => bsh_exists_rho K c)
      (by
        intro y₁ y₂ h1 h2 h3
        obtain ⟨g, hgv, hgw, hgu⟩ :=
          orthGraph_triangle hK (m := c + 3) (by omega) (bsh_hvw K c) (bsh_hwu K c)
            (bsh_huv K c) h1 h2 h3
        exact ⟨(), g, hgv, hgw, hgu⟩)
      (bshPhiV K c ψ₀) (bshPhiE K c F ψ₀ hcommE)
      (fun _ => bshPhiT K c F ψ₀ hcommT)
      (bsh_hve K c F ψ₀ hcommE) (fun _ => bsh_hvt K c F ψ₀ hcommT hι)
      (fun _ => bsh_het K c F ψ₀ hcommE hcommT)
  exact ⟨Φ, bsh_comp_blockEmb K c ψ₀ Φ hΦv, bsh_phi_tau K c F ψ₀ hcommE Φ hΦe⟩

end CFSG.StandardType.QTwo

end
