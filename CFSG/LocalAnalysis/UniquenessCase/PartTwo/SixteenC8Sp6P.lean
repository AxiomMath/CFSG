module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherMaximal
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixFusionOrbits

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (stabilizer)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.FusionOrbits
open Matrix
open scoped commutatorElement Matrix

private abbrev c8P : Subgroup (StatedSp 3 (ZMod 2)) :=
  stabilizer 3 (ZMod 2) (lagrangianZero 3)

@[expose] def singerMat : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 1; 1, 0, 1; 0, 1, 0]

@[expose] def singerMatInv : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 1, 0; 0, 0, 1; 1, 0, 0]

@[expose] def singerA : GL (Fin 3) (ZMod 2) :=
  ⟨singerMat, singerMatInv, by decide +kernel, by decide +kernel⟩

@[expose] def singerConjCoord (x : SixBits) : SixBits :=
  (x.2.1 + x.2.2.1, x.1 + x.2.1, x.1 + x.2.1 + x.2.2.1, x.2.2.2.2.2,
    x.1 + x.2.1 + x.2.2.1 + x.2.2.2.1 + x.2.2.2.2.2,
    x.1 + x.2.1 + x.2.2.1 + x.2.2.2.1 + x.2.2.2.2.1 + x.2.2.2.2.2)

theorem singerConjCoord_spec (x : SixBits) :
    (singerA : Matrix (Fin 3) (Fin 3) (ZMod 2)) * symMat (singerConjCoord x) *
        (singerA : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ +
        -symMat (singerConjCoord x) = symMat x := by
  revert x
  decide +kernel

private theorem c8_leviSp_mem_commutator (A : GL (Fin 3) (ZMod 2)) :
    leviSp A ∈ ⁅c8P, c8P⁆ := by
  haveI : Group.IsPerfect (GL (Fin 3) (ZMod 2)) := isPerfect_GL_three_zmod_two
  haveI : Group.IsPerfect ((leviSp : GL (Fin 3) (ZMod 2) →* StatedSp 3 (ZMod 2)).range) :=
    Group.IsPerfect.range (leviSp : GL (Fin 3) (ZMod 2) →* StatedSp 3 (ZMod 2))
  have hle : (leviSp : GL (Fin 3) (ZMod 2) →* StatedSp 3 (ZMod 2)).range ≤ c8P := by
    rintro x ⟨A', rfl⟩
    exact leviSp_mem_stabilizer A'
  have hmono : (leviSp : GL (Fin 3) (ZMod 2) →* StatedSp 3 (ZMod 2)).range ≤ ⁅c8P, c8P⁆ := by
    have h := Subgroup.commutator_mono hle hle
    rwa [Subgroup.commutator_eq_self] at h
  exact hmono ⟨A, rfl⟩

private theorem c8_tauSym_mem_commutator (C : Multiplicative (binarySymMatrices 3)) :
    tauSym 3 C ∈ ⁅c8P, c8P⁆ := by
  let x : SixBits := symEquiv C.toAdd
  have hsymx : symMat x = (C.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) := symMat_symEquiv C.toAdd
  let Bmat : binarySymMatrices 3 := ⟨symMat (singerConjCoord x), symMat_transpose _⟩
  let B : Multiplicative (binarySymMatrices 3) := Multiplicative.ofAdd Bmat
  have hBval : (B.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) = symMat (singerConjCoord x) := rfl
  have harg : Multiplicative.ofAdd ⟨(singerA : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
        (B.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
        (singerA : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ,
      congr_mem_binarySymMatrices _ _⟩ * B⁻¹ = C := by
    apply Multiplicative.ext
    rw [toAdd_mul, toAdd_inv, toAdd_ofAdd]
    apply Subtype.ext
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, Subtype.coe_mk]
    rw [hBval, ← hsymx]
    exact singerConjCoord_spec x
  have hcommB : ⁅leviSp singerA, tauSym 3 B⁆ = tauSym 3 C := by
    rw [commutatorElement_def, leviSp_mul_tauSym_mul_inv, ← map_inv, ← map_mul]
    exact congrArg (tauSym 3) harg
  rw [← hcommB]
  exact Subgroup.commutator_mem_commutator (leviSp_mem_stabilizer singerA)
    (unipotent_le_stabilizer (tauSym_mem_unipotent B))

theorem c8_commutator_stabilizer_lagrangianZero :
    ⁅stabilizer 3 (ZMod 2) (lagrangianZero 3), stabilizer 3 (ZMod 2) (lagrangianZero 3)⁆ =
      stabilizer 3 (ZMod 2) (lagrangianZero 3) := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro g hg h hh
    rw [commutatorElement_def]
    exact c8P.mul_mem (c8P.mul_mem (c8P.mul_mem hg hh) (c8P.inv_mem hg)) (c8P.inv_mem hh)
  · intro g hg
    obtain ⟨C, hC⟩ := exists_eq_leviSp_mul_tauSym_of_mem_stabilizer hg
    rw [hC]
    exact (⁅c8P, c8P⁆).mul_mem (c8_leviSp_mem_commutator _) (c8_tauSym_mem_commutator C)

theorem c8_stabilizer_lagrangianZero_maximal {A : Subgroup (StatedSp 3 (ZMod 2))}
    (hA : stabilizer 3 (ZMod 2) (lagrangianZero 3) ≤ A) :
    A = stabilizer 3 (ZMod 2) (lagrangianZero 3) ∨ A = ⊤ := by
  have hf : SymplecticFlag.flag 3 (ZMod 2) 3 = lagrangianZero 3 := by
    simp [SymplecticFlag.flag, lagrangianZero]
  rw [← hf] at hA ⊢
  exact CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.eq_of_stabilizer_flag_le le_rfl A hA

theorem c8_le_range_tauSym_of_normal {X : Subgroup (StatedSp 3 (ZMod 2))}
    (hX : X ≤ stabilizer 3 (ZMod 2) (lagrangianZero 3))
    (hXn : ∀ g ∈ stabilizer 3 (ZMod 2) (lagrangianZero 3), ∀ x ∈ X, g * x * g⁻¹ ∈ X)
    (h3 : ¬ 3 ∣ Nat.card X) : X ≤ (tauSym 3).range := by
  classical
  haveI : IsSimpleGroup (GL (Fin 3) (ZMod 2)) := isSimpleGroup_GL_three_two
  let f : c8P →* GL (Fin 3) (ZMod 2) := lagrangianLevi 3
  let X' : Subgroup c8P := X.subgroupOf c8P
  have hX'n : X'.Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hXn (g : StatedSp 3 (ZMod 2)) g.2 x hx⟩
  have hmapn : (X'.map f).Normal := hX'n.map f lagrangianLevi_surjective
  haveI : (X'.map f).Normal := hmapn
  have hker_eq : f.ker = (tauSym 3).range.subgroupOf c8P := ker_lagrangianLevi
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (X'.map f) with hbot | htop
  · intro x hx
    have hxker : (⟨x, hX hx⟩ : c8P) ∈ f.ker :=
      (Subgroup.map_eq_bot_iff (H := X') (f := f)).1 hbot (Subgroup.mem_subgroupOf.2 hx)
    rw [hker_eq, Subgroup.mem_subgroupOf] at hxker
    exact hxker
  · exfalso
    have hcard' : Nat.card X' = Nat.card X :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
    have hdvd : Nat.card (⊤ : Subgroup (GL (Fin 3) (ZMod 2))) ∣ Nat.card X := by
      rw [← hcard', ← htop]
      exact Subgroup.card_map_dvd (H := X') f
    rw [Subgroup.card_top, card_GL_three_two] at hdvd
    exact h3 (Nat.dvd_trans (by norm_num : 3 ∣ 168) hdvd)

theorem c8_mem_range_tauSym_of_commutator_mem {s : StatedSp 3 (ZMod 2)}
    (hs : s ∈ stabilizer 3 (ZMod 2) (lagrangianZero 3))
    (h : ∀ p ∈ stabilizer 3 (ZMod 2) (lagrangianZero 3), s * p * s⁻¹ * p⁻¹ ∈ (tauSym 3).range) :
    s ∈ (tauSym 3).range := by
  classical
  haveI : IsSimpleGroup (GL (Fin 3) (ZMod 2)) := isSimpleGroup_GL_three_two
  haveI : Group.IsPerfect (GL (Fin 3) (ZMod 2)) := isPerfect_GL_three_zmod_two
  have hcenter : center (GL (Fin 3) (ZMod 2)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (GL (Fin 3) (ZMod 2))) with hc | hc
    · exact hc
    · exfalso
      exact absurd (Subgroup.center_eq_top_iff.mp hc)
        (Group.IsPerfect.not_isMulCommutative (GL (Fin 3) (ZMod 2)))
  let f : c8P →* GL (Fin 3) (ZMod 2) := lagrangianLevi 3
  let s' : c8P := ⟨s, hs⟩
  have hker_eq : f.ker = (tauSym 3).range.subgroupOf c8P := ker_lagrangianLevi
  have hcomm : ∀ p : c8P, f s' * f p = f p * f s' := by
    intro p
    have hker : s' * p * s'⁻¹ * p⁻¹ ∈ f.ker := by
      rw [hker_eq, Subgroup.mem_subgroupOf]
      simpa using h (p : StatedSp 3 (ZMod 2)) p.2
    have hker1 : f (s' * p * s'⁻¹ * p⁻¹) = 1 := MonoidHom.mem_ker.1 hker
    have hcomm1 : ⁅f s', f p⁆ = 1 := by
      rw [commutatorElement_def]
      simpa only [map_mul, map_inv] using hker1
    exact commutatorElement_eq_one_iff_mul_comm.1 hcomm1
  have hcentral : f s' ∈ center (GL (Fin 3) (ZMod 2)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨p, rfl⟩ := lagrangianLevi_surjective g
    exact (hcomm p).symm
  rw [hcenter, Subgroup.mem_bot] at hcentral
  have hs'ker : s' ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    exact hcentral
  rw [hker_eq, Subgroup.mem_subgroupOf] at hs'ker
  exact hs'ker

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
