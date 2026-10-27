module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8HatDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.OuterExtraspecial
public import CFSG.LocalAnalysis.SectionRank.Ccomm.LinearTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open Matrix

private theorem c8h_psi_eq_one_iff {Γ : Type} [Group Γ] [Finite Γ] {d : Γ}
    {ψ : Γ →* GL (Fin 2) (ZMod 7)} {Oh Zh : Subgroup Γ}
    {φ : ↥Oh →* Multiplicative (Fin 2 → ZMod 7)}
    (hmod : C8HatMod 7 d ψ Oh Zh φ) (γ : Γ) :
    ψ γ = 1 ↔ ∀ (y : Γ) (hy : y ∈ Oh) (hy' : γ * y * γ⁻¹ ∈ Oh),
      φ ⟨γ * y * γ⁻¹, hy'⟩ = φ ⟨y, hy⟩ := by
  constructor
  · intro h y hy hy'
    rw [hmod.equivariant γ y hy hy', h]
    simp only [Units.val_one, Matrix.one_mulVec, ofAdd_toAdd]
  · intro h
    apply Units.ext
    apply Matrix.ext_iff_mulVec.2
    intro v
    obtain ⟨y, hy⟩ := hmod.surj (Multiplicative.ofAdd v)
    have hconj : γ * (y : Γ) * γ⁻¹ ∈ Oh := hmod.normal.conj_mem (y : Γ) y.2 γ
    have hy' : φ ⟨(y : Γ), y.2⟩ = Multiplicative.ofAdd v := hy
    have h1 := h y y.2 hconj
    rw [hmod.equivariant γ (y : Γ) y.2 hconj, hy'] at h1
    have h2 := congrArg Multiplicative.toAdd h1
    simpa using h2

private theorem c8h_pow_seven_eq_one (a : Multiplicative (Fin 2 → ZMod 7)) : a ^ 7 = 1 := by
  conv_lhs => rw [← ofAdd_toAdd a]
  rw [← ofAdd_nsmul]
  show (7 : ℕ) • (Multiplicative.toAdd a) = 0
  ext i
  simp [Pi.smul_apply, nsmul_eq_mul, show (7 : ZMod 7) = 0 from by decide]

theorem c8h_nat_props {Γ : Type} [Group Γ] [Finite Γ] {d : Γ} {ψ : Γ →* GL (Fin 2) (ZMod 7)}
    {Oh Zh : Subgroup Γ} {φ : ↥Oh →* Multiplicative (Fin 2 → ZMod 7)}
    (hmod : C8HatMod 7 d ψ Oh Zh φ) (ρ : Γ →* ↥(StatedSL 2 (ZMod 7)))
    (hρ : Function.Surjective ρ)
    (hρψ : ∀ γ : Γ, ((ρ γ : ↥(StatedSL 2 (ZMod 7))) : GL (Fin 2) (ZMod 7)) = ψ γ) :
    Oh ≤ ρ.ker ∧ Zh.relIndex Oh = 49 ∧ (∀ x ∈ Oh, ∀ y ∈ Oh, x * y * x⁻¹ * y⁻¹ ∈ Zh) ∧
      (∀ x ∈ Oh, x ^ 7 ∈ Zh) ∧
      (∀ γ : Γ, ρ γ = 1 ↔ ∀ x ∈ Oh, γ * x * γ⁻¹ * x⁻¹ ∈ Zh) ∧
      (∀ γ : Γ, ρ γ ≠ 1 → ρ γ ^ 2 = 1 → ∀ x ∈ Oh, γ * x * γ⁻¹ * x ∈ Zh) ∧
      (∀ W : Subgroup Γ, Zh ≤ W → W ≤ Oh → (∀ γ : Γ, ∀ w ∈ W, γ * w * γ⁻¹ ∈ W) →
        W = Zh ∨ W = Oh) := by
  have hρ1 : ∀ γ : Γ, ρ γ = 1 ↔ ψ γ = 1 := by
    intro γ
    constructor
    · intro h
      have h2 : ((ρ γ : ↥(StatedSL 2 (ZMod 7))) : GL (Fin 2) (ZMod 7)) = 1 := by
        rw [h]; rfl
      rwa [hρψ γ] at h2
    · intro h
      apply Subtype.ext
      rw [hρψ γ, h]
      rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x hx
    rw [MonoidHom.mem_ker, hρ1 x]
    refine (c8h_psi_eq_one_iff hmod x).2 ?_
    intro y hy hy'
    have : φ ⟨x * y * x⁻¹, hy'⟩ = φ ⟨x, hx⟩ * φ ⟨y, hy⟩ * (φ ⟨x, hx⟩)⁻¹ := by
      rw [show (⟨x * y * x⁻¹, hy'⟩ : ↥Oh) = ⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ from
        Subtype.ext rfl]
      rw [map_mul, map_mul, map_inv]
    rw [this]
    exact mul_inv_cancel_comm _ _
  ·
    have hker : φ.ker = Zh.subgroupOf Oh := by
      ext x
      simp only [MonoidHom.mem_ker, hmod.ker x, Subgroup.mem_subgroupOf]
    change (Zh.subgroupOf Oh).index = 49
    rw [← hker, Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective φ hmod.surj,
      Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_multiplicative]
    show Fintype.card (Fin 2 → ZMod 7) = 49
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    norm_num
  ·
    intro x hx y hy
    have hxy : x * y * x⁻¹ * y⁻¹ ∈ Oh :=
      mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
    apply (hmod.ker ⟨x * y * x⁻¹ * y⁻¹, hxy⟩).1
    have : φ ⟨x * y * x⁻¹ * y⁻¹, hxy⟩ =
        φ ⟨x, hx⟩ * φ ⟨y, hy⟩ * (φ ⟨x, hx⟩)⁻¹ * (φ ⟨y, hy⟩)⁻¹ := by
      rw [show (⟨x * y * x⁻¹ * y⁻¹, hxy⟩ : ↥Oh) =
        ⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹ from Subtype.ext rfl]
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    rw [this]
    have hc : φ ⟨x, hx⟩ * φ ⟨y, hy⟩ * (φ ⟨x, hx⟩)⁻¹ = φ ⟨y, hy⟩ :=
      mul_inv_cancel_comm _ _
    rw [hc]
    exact mul_inv_cancel _
  ·
    intro x hx
    have hx7 : x ^ 7 ∈ Oh := pow_mem hx 7
    apply (hmod.ker ⟨x ^ 7, hx7⟩).1
    have : φ ⟨x ^ 7, hx7⟩ = (φ ⟨x, hx⟩) ^ 7 := by
      rw [show (⟨x ^ 7, hx7⟩ : ↥Oh) = ⟨x, hx⟩ ^ 7 from Subtype.ext rfl]
      rw [map_pow]
    rw [this, c8h_pow_seven_eq_one]
  ·
    intro γ
    rw [hρ1 γ, c8h_psi_eq_one_iff hmod γ]
    constructor
    · intro h x hx
      have hx' : γ * x * γ⁻¹ ∈ Oh := hmod.normal.conj_mem x hx γ
      have hx'' : γ * x * γ⁻¹ * x⁻¹ ∈ Oh := mul_mem hx' (inv_mem hx)
      apply (hmod.ker ⟨γ * x * γ⁻¹ * x⁻¹, hx''⟩).1
      have h1 := h x hx hx'
      have : φ ⟨γ * x * γ⁻¹ * x⁻¹, hx''⟩ =
          φ ⟨γ * x * γ⁻¹, hx'⟩ * (φ ⟨x, hx⟩)⁻¹ := by
        rw [show (⟨γ * x * γ⁻¹ * x⁻¹, hx''⟩ : ↥Oh) =
          ⟨γ * x * γ⁻¹, hx'⟩ * ⟨x, hx⟩⁻¹ from Subtype.ext rfl]
        rw [map_mul, map_inv]
      rw [this, h1]
      exact mul_inv_cancel _
    · intro h y hy hy'
      have hyy : γ * y * γ⁻¹ * y⁻¹ ∈ Oh := mul_mem hy' (inv_mem hy)
      have hmem := (hmod.ker ⟨γ * y * γ⁻¹ * y⁻¹, hyy⟩).2 (h y hy)
      have : φ ⟨γ * y * γ⁻¹ * y⁻¹, hyy⟩ =
          φ ⟨γ * y * γ⁻¹, hy'⟩ * (φ ⟨y, hy⟩)⁻¹ := by
        rw [show (⟨γ * y * γ⁻¹ * y⁻¹, hyy⟩ : ↥Oh) =
          ⟨γ * y * γ⁻¹, hy'⟩ * ⟨y, hy⟩⁻¹ from Subtype.ext rfl]
        rw [map_mul, map_inv]
      rw [this] at hmem
      exact mul_inv_eq_one.1 hmem
  ·
    intro γ hne hsq x hx
    let M : Matrix (Fin 2) (Fin 2) (ZMod 7) :=
      ((ρ γ : ↥(StatedSL 2 (ZMod 7))) : GL (Fin 2) (ZMod 7))
    have hMdet : M.det = 1 := by
      simpa only [M] using CFSG.Open.StatedAPI.det_of_mem_statedSL (ρ γ).2
    have hMM : M * M = 1 := by
      have h := congrArg (fun A : ↥(StatedSL 2 (ZMod 7)) =>
        ((A : GL (Fin 2) (ZMod 7)) : Matrix (Fin 2) (Fin 2) (ZMod 7))) hsq
      simpa [M, pow_two, SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val] using h
    have hcases := CFSG.SectionRank.Ccomm.eq_one_or_neg_one_of_sq_eq_one
      (k := ZMod 7) (by decide : (2 : ZMod 7) ≠ 0) hMdet hMM
    have hMneg : M = -1 := by
      rcases hcases with h | h
      · exfalso
        apply hne
        apply Subtype.ext
        apply Units.ext
        have h' : (((ρ γ : ↥(StatedSL 2 (ZMod 7))) : GL (Fin 2) (ZMod 7)) :
            Matrix (Fin 2) (Fin 2) (ZMod 7)) = 1 := by
          simpa only [M] using h
        exact h'
      · exact h
    have hψ : (ψ γ : Matrix (Fin 2) (Fin 2) (ZMod 7)) = -1 := by
      rw [← hρψ γ]
      simpa only [M] using hMneg
    have hx' : γ * x * γ⁻¹ ∈ Oh := hmod.normal.conj_mem x hx γ
    have hx2 : γ * x * γ⁻¹ * x ∈ Oh := mul_mem hx' hx
    apply (hmod.ker ⟨γ * x * γ⁻¹ * x, hx2⟩).1
    have h1 := hmod.equivariant γ x hx hx'
    have hneg : ((-1 : Matrix (Fin 2) (Fin 2) (ZMod 7))).mulVec
        (Multiplicative.toAdd (φ ⟨x, hx⟩)) = -(Multiplicative.toAdd (φ ⟨x, hx⟩)) := by
      have h := Matrix.neg_mulVec (A := (1 : Matrix (Fin 2) (Fin 2) (ZMod 7)))
        (v := Multiplicative.toAdd (φ ⟨x, hx⟩))
      rw [Matrix.one_mulVec] at h
      exact h
    have h1' : φ ⟨γ * x * γ⁻¹, hx'⟩ = (φ ⟨x, hx⟩)⁻¹ := by
      rw [h1, hψ]
      exact (congrArg Multiplicative.ofAdd hneg).trans (ofAdd_neg _)
    have : φ ⟨γ * x * γ⁻¹ * x, hx2⟩ = φ ⟨γ * x * γ⁻¹, hx'⟩ * φ ⟨x, hx⟩ := by
      rw [show (⟨γ * x * γ⁻¹ * x, hx2⟩ : ↥Oh) = ⟨γ * x * γ⁻¹, hx'⟩ * ⟨x, hx⟩ from
        Subtype.ext rfl]
      rw [map_mul]
    rw [this, h1']
    exact inv_mul_cancel _
  ·
    intro W hZW hWOh hWin
    set S : Subgroup (Multiplicative (Fin 2 → ZMod 7)) := (W.subgroupOf Oh).map φ with hSdef
    have hVinv : ∀ A ∈ StatedSL 2 (ZMod 7), ∀ w ∈ Subgroup.toAddSubgroup' S,
        Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) (ZMod 7)) w ∈ Subgroup.toAddSubgroup' S := by
      intro A hA w hw
      have hwS : Multiplicative.ofAdd w ∈ S := (Subgroup.mem_toAddSubgroup' S w).1 hw
      rw [hSdef, Subgroup.mem_map] at hwS
      obtain ⟨u, hu, huφ⟩ := hwS
      have huφ' : φ ⟨(u : Γ), u.2⟩ = Multiplicative.ofAdd w := huφ
      have huW : (u : Γ) ∈ W := (Subgroup.mem_subgroupOf).1 hu
      obtain ⟨γ, hγ⟩ := hρ (⟨A, hA⟩ : ↥(StatedSL 2 (ZMod 7)))
      have hψA : (ψ γ : Matrix (Fin 2) (Fin 2) (ZMod 7)) = A := by
        rw [← hρψ γ, hγ]
      have hconj : γ * (u : Γ) * γ⁻¹ ∈ W := hWin γ u huW
      have hconjOh : γ * (u : Γ) * γ⁻¹ ∈ Oh := hWOh hconj
      have heq := hmod.equivariant γ (u : Γ) u.2 hconjOh
      rw [huφ', toAdd_ofAdd, hψA] at heq
      have hmemS : Multiplicative.ofAdd
          (Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) (ZMod 7)) w) ∈ S := by
        rw [← heq, hSdef]
        exact Subgroup.mem_map_of_mem φ (show (⟨γ * (u : Γ) * γ⁻¹, hconjOh⟩ : ↥Oh) ∈
          W.subgroupOf Oh from (Subgroup.mem_subgroupOf).2 hconj)
      exact (Subgroup.mem_toAddSubgroup' S _).2 hmemS
    have hVT := CFSG.LocalAnalysis.RankThreeTheoremC.eq_bot_or_eq_top_of_forall_mulVec_mem
      (Subgroup.toAddSubgroup' S) hVinv
    rcases hVT with hVbot | hVtop
    · left
      have hSbot : S = ⊥ := by
        have h1 : Subgroup.toAddSubgroup' S =
            Subgroup.toAddSubgroup' (⊥ : Subgroup (Multiplicative (Fin 2 → ZMod 7))) := by
          rw [hVbot, OrderIso.map_bot]
        exact Subgroup.toAddSubgroup'.injective h1
      apply le_antisymm _ hZW
      intro w hw
      have hwOh : w ∈ Oh := hWOh hw
      have hwS : φ ⟨w, hwOh⟩ ∈ S := by
        rw [hSdef]
        exact Subgroup.mem_map_of_mem φ ((Subgroup.mem_subgroupOf).2 hw)
      rw [hSbot] at hwS
      exact (hmod.ker ⟨w, hwOh⟩).1 (Subgroup.mem_bot.1 hwS)
    · right
      have hStop : S = ⊤ := by
        have h1 : Subgroup.toAddSubgroup' S =
            Subgroup.toAddSubgroup' (⊤ : Subgroup (Multiplicative (Fin 2 → ZMod 7))) := by
          rw [hVtop, OrderIso.map_top]
        exact Subgroup.toAddSubgroup'.injective h1
      apply le_antisymm hWOh
      intro x hx
      have hxS : φ ⟨x, hx⟩ ∈ S := by rw [hStop]; trivial
      rw [hSdef, Subgroup.mem_map] at hxS
      obtain ⟨u, hu, huφ⟩ := hxS
      have huW : (u : Γ) ∈ W := (Subgroup.mem_subgroupOf).1 hu
      have hux : (u : Γ)⁻¹ * x ∈ Oh := mul_mem (inv_mem u.2) hx
      have hmemZh : (u : Γ)⁻¹ * x ∈ Zh := by
        apply (hmod.ker ⟨(u : Γ)⁻¹ * x, hux⟩).1
        have hfac : φ ⟨(u : Γ)⁻¹ * x, hux⟩ = (φ u)⁻¹ * φ ⟨x, hx⟩ := by
          rw [show (⟨(u : Γ)⁻¹ * x, hux⟩ : ↥Oh) = u⁻¹ * ⟨x, hx⟩ from Subtype.ext rfl]
          rw [map_mul, map_inv]
        rw [hfac, huφ]
        exact inv_mul_cancel _
      have hmemW : (u : Γ) * ((u : Γ)⁻¹ * x) ∈ W := mul_mem huW (hZW hmemZh)
      simpa using hmemW

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
