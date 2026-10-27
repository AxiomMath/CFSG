module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshData
public import CFSG.Certificates.Kernel.Yosh26900Norm
public import CFSG.CharacterTheory.Blocks.Defs
public import CFSG.GH74.M12.Reductions
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Data
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh.Spec

open Equiv Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.GH74.M12

@[expose] noncomputable def yK : Subgroup (Perm (Fin 14)) := closure (tp 14 '' {x | x ∈ yGens})

@[expose] noncomputable def tK : Subgroup (Perm (Fin 14)) := closure (tp 14 '' {x | x ∈ tGens})

theorem tp_mem_yK {x : Table} (hx : x ∈ yGens) : tp 14 x ∈ yK := subset_closure ⟨x, hx, rfl⟩

theorem tK_le : tK ≤ yK := by
  rw [tK, closure_le]
  rintro _ ⟨x, hx, rfl⟩
  refine tp_mem_yK ?_
  have hx' : x ∈ tGens := hx
  simp only [tGens, Array.mem_def, List.mem_cons, List.not_mem_nil, or_false] at hx'
  rcases hx' with rfl | rfl | rfl | rfl <;> simp [yGens]

@[expose] noncomputable def eK : ↥yK := ⟨tp 14 tauT, tp_mem_yK (by simp [yGens])⟩

@[expose] noncomputable def fK : ↥yK := ⟨tp 14 (tbl14 bfF), tp_mem_yK (by simp [yGens])⟩

@[expose] noncomputable def cK : ↥yK := fK ^ 4

@[expose] noncomputable def sK : ↥yK := ⟨tp 14 sT, tp_mem_yK (by simp [yGens, sT])⟩

@[expose] def epsY (y : Perm (Fin 14)) : ℕ := if ((y 12 : Fin 14) : ℕ) = 13 then 1 else 0

@[expose] def yv (y : Perm (Fin 14)) (j : ℕ) : ℕ := if h : j < 14 then (y ⟨j, h⟩ : ℕ) else j

@[expose] def lamY (y : Perm (Fin 14)) : ℕ :=
  ∑ j ∈ Finset.range 4, ∑ i ∈ Finset.range j, if yv y j < yv y i then 1 else 0

@[expose] def SwapType (ψ : MulAut ↥yK) (u : ↥yK) : Prop :=
  Nat.card {t : ↥yK // (t : Perm (Fin 14)) ∈ tK ∧ t * u = u * t} +
      Nat.card {t : ↥yK // (t : Perm (Fin 14)) ∈ tK ∧ t * ψ u = u * t} = 128 ∧
    (∀ t : ↥yK, (t : Perm (Fin 14)) ∈ tK → t * u = u * t → t ^ 4 = 1) ∧
    ∀ t : ↥yK, (t : Perm (Fin 14)) ∈ tK → t * ψ u = u * t → (t * ψ t) ^ 2 = 1

@[expose] def IsYoshAut (ψ : MulAut ↥yK) : Prop :=
  ψ eK = eK * cK ∧ ψ cK = cK ∧ ψ sK = sK ∧ ∀ y, ψ (ψ y) = y

structure Facts : Prop where
  card_yK : Nat.card yK = 384
  card_tK : Nat.card tK = 128
  u1_mem : tp 14 u1T ∈ tK
  t8 : ∃ t ∈ tK, t ^ 4 ≠ 1
  e_sq : eK ^ 2 = 1
  c_sq : cK ^ 2 = 1
  c_ne_one : cK ≠ 1
  s_cube : sK ^ 3 = 1
  s_ne_one : sK ≠ 1
  e_comm : ∀ y, eK * y = y * eK
  c_comm : ∀ y, cK * y = y * cK
  cent_s : ∀ z, z * sK = sK * z → ∃ a b r : ℕ, z = eK ^ a * cK ^ b * sK ^ r
  inv_s : ∃ n, n * sK = sK * sK * n
  syl_s : ∀ z : ↥yK, z ^ 3 = 1 → z ≠ 1 → ∃ h, h * z = sK * h ∨ h * z = sK * sK * h
  classify : ∀ ψ : MulAut ↥yK, IsYoshAut ψ →
    (∀ y : ↥yK, ψ y = y * cK ^ epsY y) ∨ (∀ y : ↥yK, ψ y = y * cK ^ (epsY y + lamY y)) ∨
      ∀ u : ↥yK, (u : Perm (Fin 14)) = tp 14 tauT * tp 14 u1T → SwapType ψ u
  pt : ∀ ψ : MulAut ↥yK, IsYoshAut ψ → ∀ y : ↥yK, (y : Perm (Fin 14)) ∈ tK →
    (ψ y : Perm (Fin 14)) ∈ tK

theorem Facts.norm (hF : Facts) (ψ : MulAut ↥yK) (he : ψ eK = eK * cK) (hc : ψ cK = cK)
    (w : ↥yK) (hw : ψ w = w) (hw2 : ∀ y, ψ (ψ y) * w = w * y) :
    ∃ h : ↥yK, h * ψ sK = sK * h ∧ h * ψ h * w = 1 :=
  CFSG.KC.Yosh26900.norm_swap eK cK sK hF.e_sq hF.c_sq hF.c_ne_one hF.s_cube hF.s_ne_one hF.e_comm
    hF.c_comm hF.cent_s (by
      obtain ⟨n, hn⟩ := hF.inv_s
      exact ⟨n, hn⟩)
    (fun z h3 h1 => hF.syl_s z h3 h1) ψ he hc w hw hw2

end CFSG.EvenSporadicStandard.M12Std.Yosh.Spec

end
