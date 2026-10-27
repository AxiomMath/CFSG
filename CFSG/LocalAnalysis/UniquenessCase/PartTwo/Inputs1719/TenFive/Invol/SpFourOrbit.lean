module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.SpLevi
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Defs
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFourSylow
import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherParabolicData
import CFSG.LocalAnalysis.ComponentInitial.SymplecticSixCoverModel
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.DParam
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Open Subgroup Matrix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj upperUnipotentSp)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (spScalars)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (leviSp)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticSixCover (leviSp_mul_upperUnipotentSp_mul_inv)

variable {K : Type} [Field K]
variable {p : ℕ}

private theorem tau_zero :
    tau (C := (0 : Matrix (Fin 2) (Fin 2) K)) transpose_zero = 1 := by
  apply CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.statedSp_ext
  rw [coe_tau, fromBlocks_one]
  rfl

private theorem inv_tau {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) :
    (tau hC)⁻¹ = tau (C := -C) (by rw [transpose_neg, hC]) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [tau_mul_tau]
  exact (tau_congr _ _ (add_neg_cancel C)).trans tau_zero

private theorem transpose_nsmul {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) (n : ℕ) :
    (n • C)ᵀ = n • C := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, transpose_add, ih, hC]

private theorem tau_pow {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) (n : ℕ) :
    tau hC ^ n = tau (C := n • C) (transpose_nsmul hC n) := by
  induction n with
  | zero =>
      rw [pow_zero]
      exact ((tau_congr (transpose_nsmul hC 0) transpose_zero (zero_nsmul C)).trans tau_zero).symm
  | succ n ih =>
      rw [pow_succ, ih, tau_mul_tau]
      exact tau_congr _ _ (succ_nsmul C n).symm

private theorem tau_pow_eq_one {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) [CharP K p] :
    tau hC ^ p = 1 := by
  rw [tau_pow]
  have hp0 : (p : K) = 0 := CharP.cast_eq_zero K p
  have hzero : p • C = 0 := by
    ext i j
    show p • C i j = 0
    rw [nsmul_eq_mul, hp0, zero_mul]
  exact (tau_congr _ _ hzero).trans tau_zero

private theorem isElemAbelian_radical [CharP K p] :
    IsElemAbelian p (radical K) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨C, hC, ha⟩ := a.2
    obtain ⟨E, hE, hb⟩ := b.2
    exact Subtype.ext (by
      show (a : StatedSp 2 K) * b = b * a
      rw [ha, hb, tau_comm hC hE])
  · obtain ⟨C, hC, rfl⟩ := hx
    exact tau_pow_eq_one hC

private noncomputable def Urad : Subgroup (StatedProj (StatedSp 2 K)) :=
  (radical K).map (proj 2 K)

private theorem symAdd_transpose (C : symAdd K) : (C.1)ᵀ = C.1 := C.2

private theorem psi_mem (C : symAdd K) : proj 2 K (tau (symAdd_transpose C)) ∈ Urad (K := K) :=
  Subgroup.mem_map_of_mem (proj 2 K) ⟨C.1, C.2, rfl⟩

private noncomputable def psi (C : symAdd K) : Urad (K := K) :=
  ⟨proj 2 K (tau (symAdd_transpose C)), psi_mem C⟩

private theorem psi_mul (C E : symAdd K) : psi (C + E) = psi C * psi E := by
  apply Subtype.ext
  change proj 2 K (tau (symAdd_transpose (C + E))) =
    proj 2 K (tau (symAdd_transpose C)) * proj 2 K (tau (symAdd_transpose E))
  rw [← map_mul]
  have h : tau (symAdd_transpose (C + E)) =
      tau (symAdd_transpose C) * tau (symAdd_transpose E) := by
    rw [← tau_mul_tau (symAdd_transpose C) (symAdd_transpose E)]
  rw [h]

private theorem psi_one : psi (0 : symAdd K) = 1 := by
  apply Subtype.ext
  change proj 2 K (tau (symAdd_transpose (0 : symAdd K))) = 1
  have h : tau (symAdd_transpose (0 : symAdd K)) = 1 :=
    (tau_congr _ _ rfl).trans tau_zero
  rw [h, map_one]

private noncomputable def psiAdd : symAdd K →+ Additive (Urad (K := K)) where
  toFun C := Additive.ofMul (psi C)
  map_zero' := by
    apply Additive.ext
    exact psi_one
  map_add' C E := by
    apply Additive.ext
    exact psi_mul C E

private theorem psi_inj : Function.Injective (psi (K := K)) := by
  intro C E h
  have hval : proj 2 K (tau (symAdd_transpose C)) =
      proj 2 K (tau (symAdd_transpose E)) := congrArg Subtype.val h
  have hker : (tau (symAdd_transpose C))⁻¹ * tau (symAdd_transpose E) ∈
      spScalars 2 K := QuotientGroup.eq.mp hval
  have htau : (tau (symAdd_transpose C))⁻¹ * tau (symAdd_transpose E) =
      tau (C := E.1 - C.1)
        (by rw [transpose_sub, symAdd_transpose C, symAdd_transpose E]) := by
    rw [inv_tau]
    rw [tau_mul_tau (show (-C.1)ᵀ = -C.1 by rw [transpose_neg, symAdd_transpose C])
      (symAdd_transpose E)]
    exact tau_congr _ _ (by rw [sub_eq_add_neg, add_comm])
  rw [htau, Subgroup.mem_subgroupOf] at hker
  obtain ⟨c, hc⟩ := hker
  have hm : Matrix.scalar (Fin 2 ⊕ Fin 2) (c : K) = fromBlocks 1 (E.1 - C.1) 0 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_scalar, hc, coe_tau]
  have hzero : E.1 - C.1 = 0 := by
    ext i j
    have h := congrFun₂ hm (Sum.inl i) (Sum.inr j)
    simpa [Matrix.scalar_apply, Matrix.fromBlocks_apply₁₂] using h.symm
  exact Subtype.ext (sub_eq_zero.mp hzero).symm

private theorem psiAdd_inj : Function.Injective (psiAdd (K := K)) := by
  intro C E h
  exact psi_inj (congrArg Additive.toMul h)

private theorem psiAdd_surj : Function.Surjective (psiAdd (K := K)) := by
  intro u
  obtain ⟨r, hr, hproj⟩ := Subgroup.mem_map.mp (Additive.toMul u).2
  obtain ⟨C, hC, rfl⟩ := hr
  refine ⟨⟨C, hC⟩, ?_⟩
  apply Additive.ext
  exact Subtype.ext hproj


private noncomputable def nLevi (g : GL (Fin 2) K) : StatedProj (StatedSp 2 K) :=
  proj 2 K (leviSp g)

private theorem nLevi_inv (g : GL (Fin 2) K) : nLevi g⁻¹ = (nLevi g)⁻¹ := by
  simp [nLevi]

private theorem levAct_transpose (g : GL (Fin 2) K) {C : Matrix (Fin 2) (Fin 2) K}
    (hC : Cᵀ = C) : (levAct g C)ᵀ = levAct g C := by
  simp only [levAct, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [transpose_mul, transpose_mul, transpose_transpose, hC, Matrix.mul_assoc]

private theorem leviSp_mul_tau_mul_inv (g : GL (Fin 2) K)
    {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) :
    leviSp g * tau hC * (leviSp g)⁻¹ =
      tau (C := (g : Matrix (Fin 2) (Fin 2) K) * C * (g : Matrix (Fin 2) (Fin 2) K)ᵀ)
        (by rw [transpose_mul, transpose_mul, transpose_transpose, hC, Matrix.mul_assoc]) := by
  change leviSp g * upperUnipotentSp 2 K hC * (leviSp g)⁻¹ =
    upperUnipotentSp 2 K (by
      rw [transpose_mul, transpose_mul, transpose_transpose, hC, Matrix.mul_assoc])
  exact leviSp_mul_upperUnipotentSp_mul_inv (n := 2) (K := K) g hC

private theorem psi_levAct (g : GL (Fin 2) K) (C : symAdd K) :
    (psi ⟨levAct g C.1, levAct_transpose g (symAdd_transpose C)⟩ :
        StatedProj (StatedSp 2 K)) = nLevi g * (psi C : StatedProj (StatedSp 2 K)) *
      (nLevi g)⁻¹ := by
  show proj 2 K (tau (C := levAct g C.1) (levAct_transpose g (symAdd_transpose C))) =
    proj 2 K (leviSp g) * proj 2 K (tau (symAdd_transpose C)) * (proj 2 K (leviSp g))⁻¹
  rw [← map_inv, ← map_mul, ← map_mul]
  rw [leviSp_mul_tau_mul_inv]
  exact congrArg (proj 2 K) (tau_congr _ _ rfl)

private theorem levAct_mul (g h : GL (Fin 2) K) (C : Matrix (Fin 2) (Fin 2) K) :
    levAct g (levAct h C) = levAct (g * h) C := by
  simp only [levAct, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Units.val_mul, transpose_mul]
  noncomm_ring

private theorem levAct_one (C : Matrix (Fin 2) (Fin 2) K) : levAct 1 C = C := by
  simp [levAct]

private theorem levAct_levAct_inv (g : GL (Fin 2) K) (C : Matrix (Fin 2) (Fin 2) K) :
    levAct g (levAct g⁻¹ C) = C := by
  rw [levAct_mul, mul_inv_cancel, levAct_one]

private theorem levAct_inv_levAct (g : GL (Fin 2) K) (C : Matrix (Fin 2) (Fin 2) K) :
    levAct g⁻¹ (levAct g C) = C := by
  rw [levAct_mul, inv_mul_cancel, levAct_one]

private theorem mem_map_conj_iff (D₀ : Subgroup (StatedProj (StatedSp 2 K)))
    (n x : StatedProj (StatedSp 2 K)) :
    x ∈ D₀.map (MulAut.conj n).toMonoidHom ↔ n⁻¹ * x * n ∈ D₀ := by
  constructor
  · intro h
    rw [Subgroup.mem_map] at h
    obtain ⟨d, hd, hdconj⟩ := h
    have hdconj' : n * d * n⁻¹ = x := hdconj
    have heq : n⁻¹ * x * n = d := by rw [← hdconj']; group
    rwa [heq]
  · intro h
    rw [Subgroup.mem_map]
    refine ⟨n⁻¹ * x * n, h, ?_⟩
    show n * (n⁻¹ * x * n) * n⁻¹ = x
    group

private noncomputable def H0as (D₀ : Subgroup (StatedProj (StatedSp 2 K))) :
    AddSubgroup (symAdd K) :=
  AddSubgroup.comap (psiAdd (K := K)) (Subgroup.toAddSubgroup (D₀.subgroupOf (Urad (K := K))))

private noncomputable def H0 (D₀ : Subgroup (StatedProj (StatedSp 2 K))) :
    AddSubgroup (Matrix (Fin 2) (Fin 2) K) :=
  (H0as D₀).map (symAdd K).subtype

private theorem H0_le (D₀ : Subgroup (StatedProj (StatedSp 2 K))) :
    H0 D₀ ≤ symAdd K := by
  intro C hC
  rw [H0] at hC
  obtain ⟨x, -, rfl⟩ := AddSubgroup.mem_map.mp hC
  exact x.2

private theorem H0_relIndex (D₀ : Subgroup (StatedProj (StatedSp 2 K))) :
    (H0 D₀).relIndex (symAdd K) = D₀.relIndex (Urad (K := K)) := by
  have htop : (⊤ : AddSubgroup (symAdd K)).map (symAdd K).subtype = symAdd K := by
    rw [AddSubgroup.map_top, AddSubgroup.range_subtype]
  have hmap : (H0 D₀).relIndex (symAdd K) = (H0as D₀).relIndex ⊤ := by
    rw [H0]
    have h := AddSubgroup.relIndex_map_map_of_injective (f := (symAdd K).subtype)
      (fun x y hxy => Subtype.ext hxy) (H := H0as D₀) (K := ⊤)
    rwa [htop] at h
  rw [hmap, AddSubgroup.relIndex_top_right, H0as, AddSubgroup.index_comap]
  rw [AddMonoidHom.range_eq_top.mpr psiAdd_surj, AddSubgroup.relIndex_top_right,
    Subgroup.index_toAddSubgroup]
  rfl

private theorem mem_H0_iff (D₀ : Subgroup (StatedProj (StatedSp 2 K))) (C : symAdd K) :
    (C : Matrix (Fin 2) (Fin 2) K) ∈ H0 D₀ ↔ (psi C : StatedProj (StatedSp 2 K)) ∈ D₀ := by
  constructor
  · intro hC
    rw [H0] at hC
    obtain ⟨x, hx, hxeq⟩ := AddSubgroup.mem_map.mp hC
    have hxC : x = C := Subtype.ext hxeq
    subst hxC
    rw [H0as, AddSubgroup.mem_comap, Additive.mem_toAddSubgroup] at hx
    rw [Subgroup.mem_subgroupOf] at hx
    exact hx
  · intro hC
    rw [H0]
    refine AddSubgroup.mem_map.mpr ⟨C, ?_, rfl⟩
    rw [H0as, AddSubgroup.mem_comap, Additive.mem_toAddSubgroup, Subgroup.mem_subgroupOf]
    exact hC

private theorem mem_H0_map_levAct_iff (D₀ : Subgroup (StatedProj (StatedSp 2 K)))
    (g : GL (Fin 2) K) (C : symAdd K) :
    (C : Matrix (Fin 2) (Fin 2) K) ∈ (H0 D₀).map (levAct g) ↔
      (psi C : StatedProj (StatedSp 2 K)) ∈
        D₀.map (MulAut.conj (nLevi g)).toMonoidHom := by
  have hleft : (C : Matrix (Fin 2) (Fin 2) K) ∈ (H0 D₀).map (levAct g) ↔
      (psi ⟨levAct g⁻¹ C.1, levAct_transpose g⁻¹ (symAdd_transpose C)⟩ :
        StatedProj (StatedSp 2 K)) ∈ D₀ := by
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨x, hx, hxeq⟩
      have hxC : x = levAct g⁻¹ C.1 := by
        have h := congrArg (levAct g⁻¹) hxeq
        rwa [levAct_inv_levAct] at h
      have hx_sym : x ∈ symAdd K := H0_le D₀ hx
      rw [hxC] at hx
      exact (mem_H0_iff D₀ ⟨levAct g⁻¹ C.1, levAct_transpose g⁻¹ (symAdd_transpose C)⟩).mp hx
    · intro h
      exact ⟨_, (mem_H0_iff D₀ ⟨levAct g⁻¹ C.1,
        levAct_transpose g⁻¹ (symAdd_transpose C)⟩).mpr h, levAct_levAct_inv g C.1⟩
  rw [hleft, mem_map_conj_iff, psi_levAct, nLevi_inv, inv_inv]

private theorem conj_mem_Urad (g : GL (Fin 2) K) {h : StatedProj (StatedSp 2 K)}
    (hh : h ∈ Urad (K := K)) : nLevi g * h * (nLevi g)⁻¹ ∈ Urad (K := K) := by
  obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hh
  obtain ⟨C, hC, rfl⟩ := hr
  have hval : (psi ⟨C, hC⟩ : StatedProj (StatedSp 2 K)) = proj 2 K (tau hC) := rfl
  rw [← hval, ← psi_levAct g ⟨C, hC⟩]
  exact (psi ⟨levAct g C, levAct_transpose g hC⟩).2

private theorem nLevi_mem_normalizer (g : GL (Fin 2) K) :
    nLevi g ∈ Subgroup.normalizer (Urad (K := K) : Set (StatedProj (StatedSp 2 K))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact conj_mem_Urad g
  · intro hh
    have hh' := conj_mem_Urad g⁻¹ hh
    have heq : nLevi g⁻¹ * (nLevi g * h * (nLevi g)⁻¹) * (nLevi g⁻¹)⁻¹ = h := by
      rw [nLevi_inv, inv_inv]
      group
    rwa [heq] at hh'

theorem isOrbitGood_tau [Finite K] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [CharP K p]
    (hK : Nat.card K = p ^ e) (h3 : 3 < p ^ e) {S₀ : Matrix (Fin 2) (Fin 2) K} (hS₀ : S₀ᵀ = S₀)
    (haniso : ∀ v : Fin 2 → K, v ≠ 0 → v ⬝ᵥ (S₀ *ᵥ v) ≠ 0) :
    IsOrbitGood p (proj 2 K (tau hS₀)) := by
  classical
  have he : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · rw [h, pow_zero] at h3
      omega
    · exact h
  have he3 : p = 3 → 2 ≤ e := by
    intro hp3
    have hne1 : e ≠ 1 := by
      intro he1
      rw [hp3, he1, pow_one] at h3
      omega
    omega
  refine ⟨Urad (K := K), p ^ e, ?_, ?_, ?_, ?_⟩
  · exact psi_mem ⟨S₀, hS₀⟩
  · exact CFSG.Open.IsElemAbelian.map (isElemAbelian_radical (K := K)) (proj 2 K)
  · exact sixteen_le_pow_mul_dParam hp hp2 he he3
  · intro D₀ hD₀ hidx
    have hH0 : H0 D₀ ≤ symAdd K := H0_le D₀
    have hidxH : (H0 D₀).relIndex (symAdd K) = p := by
      rw [H0_relIndex, hidx]
    have hcount := le_ncard_levAct hp hp2 hK h3 hS₀ haniso hH0 hidxH
    let 𝓗 : Set (AddSubgroup (Matrix (Fin 2) (Fin 2) K)) :=
      {H | S₀ ∉ H ∧ ∃ g : GL (Fin 2) K, H = (H0 D₀).map (levAct g)}
    let T : Set (Subgroup (StatedProj (StatedSp 2 K))) :=
      {D | proj 2 K (tau hS₀) ∉ D ∧ ∃ g ∈ Subgroup.normalizer
        (Urad (K := K) : Set (StatedProj (StatedSp 2 K))),
          D = D₀.map (MulAut.conj g).toMonoidHom}
    let F : AddSubgroup (Matrix (Fin 2) (Fin 2) K) → Subgroup (StatedProj (StatedSp 2 K)) :=
      fun H => if hH : H ∈ 𝓗 then
        D₀.map (MulAut.conj (nLevi (Classical.choose hH.2))).toMonoidHom else ⊥
    have hF_def : ∀ (H : AddSubgroup (Matrix (Fin 2) (Fin 2) K)) (hH : H ∈ 𝓗),
        F H = D₀.map (MulAut.conj (nLevi (Classical.choose hH.2))).toMonoidHom := by
      intro H hH
      show (if h : H ∈ 𝓗 then _ else ⊥) = _
      exact dif_pos hH
    have hFmem : ∀ H ∈ 𝓗, F H ∈ T := by
      intro H hH
      rw [hF_def H hH]
      refine ⟨?_, nLevi (Classical.choose hH.2), nLevi_mem_normalizer _, rfl⟩
      intro hx
      have hx' : (psi ⟨S₀, hS₀⟩ : StatedProj (StatedSp 2 K)) ∈
          D₀.map (MulAut.conj (nLevi (Classical.choose hH.2))).toMonoidHom := by
        simpa [psi] using hx
      have hS0mem : S₀ ∈ (H0 D₀).map (levAct (Classical.choose hH.2)) :=
        (mem_H0_map_levAct_iff D₀ (Classical.choose hH.2) ⟨S₀, hS₀⟩).mpr hx'
      rw [← Classical.choose_spec hH.2] at hS0mem
      exact hH.1 hS0mem
    have hFinj : Set.InjOn F 𝓗 := by
      intro H₁ hH₁ H₂ hH₂ hEq
      have hmem : ∀ (H : AddSubgroup (Matrix (Fin 2) (Fin 2) K)) (hH : H ∈ 𝓗) (C : symAdd K),
          (C : Matrix (Fin 2) (Fin 2) K) ∈ H ↔
            (psi C : StatedProj (StatedSp 2 K)) ∈
              D₀.map (MulAut.conj (nLevi (Classical.choose hH.2))).toMonoidHom := by
        intro H hH C
        set g := Classical.choose hH.2 with hg
        have hspec : H = (H0 D₀).map (levAct g) := by
          rw [hg]
          exact Classical.choose_spec hH.2
        calc (C : Matrix (Fin 2) (Fin 2) K) ∈ H ↔
              (C : Matrix (Fin 2) (Fin 2) K) ∈ (H0 D₀).map (levAct g) := by rw [hspec]
          _ ↔ (psi C : StatedProj (StatedSp 2 K)) ∈
              D₀.map (MulAut.conj (nLevi g)).toMonoidHom :=
            mem_H0_map_levAct_iff D₀ g C
      rw [hF_def H₁ hH₁, hF_def H₂ hH₂] at hEq
      have hle : ∀ (H : AddSubgroup (Matrix (Fin 2) (Fin 2) K)) (hH : H ∈ 𝓗),
          H ≤ symAdd K := by
        intro H hH
        rw [Classical.choose_spec hH.2]
        intro x hx
        rw [AddSubgroup.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        exact levAct_transpose _ (H0_le D₀ hy)
      apply AddSubgroup.ext
      intro C
      by_cases hC : C ∈ symAdd K
      · have e₁ := hmem H₁ hH₁ ⟨C, hC⟩
        have e₂ := hmem H₂ hH₂ ⟨C, hC⟩
        rw [e₁, e₂, hEq]
      · exact ⟨fun h => absurd (hle H₁ hH₁ h) hC, fun h => absurd (hle H₂ hH₂ h) hC⟩
    have hle : 𝓗.ncard ≤ T.ncard :=
      Set.ncard_le_ncard_of_injOn F hFmem hFinj (Set.toFinite T)
    exact hcount.trans hle


end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
