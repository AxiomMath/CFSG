module

public import CFSG.Monster.Existence.StdOdd.Cert.Lie
public import Certificates.Data.CFSGNative.Chevalley.C2E6CertOrbit
public meta import Certificates.Data.CFSGNative.Chevalley.C2E6StdMatrix
public meta import Certificates.Data.CFSGNative.Chevalley.C2E6CertLie
public meta import Certificates.Data.CFSGNative.Chevalley.C2E6CertOrbit
public meta import CFSG.LieType.Chevalley.C2E6StdMatrixData
public meta import CFSG.Monster.B.Classical.E6AdjointTable
import all CFSG.LieType.Chevalley.C2E6StdMatrixModel
public import CFSG.LieType.Chevalley.C2E6StdMatrixVec
public import CFSG.LieType.Chevalley.C2E6StdMatrixModelInputs
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate117
public import Certificates.Certificate10004

public section

namespace CFSG.Monster.Existence.StdOdd.Cert

open CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.MatrixModel
  CFSG.Monster.Existence.StdOdd CFSG.Monster.Existence.StdOdd.CertNative
  CFSG.LieType.Chevalley.C2E6Overlap CFSG.Monster.B.Classical.E6Adjoint

theorem inv_smul_mem
    {S : Set Pt} {g : Rgrp} (hg : ∀ x ∈ S, g • x ∈ S) :
    ∀ x ∈ S, g⁻¹ • x ∈ S := by
  have hpow : ∀ n : ℕ, ∀ x ∈ S, (g ^ n) • x ∈ S := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih => intro x hx; rw [pow_succ, mul_smul]; exact ih _ (hg x hx)
  intro x hx
  have hpos : 0 < orderOf g := orderOf_pos g
  have h1 : g⁻¹ = g ^ (orderOf g - 1) := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
  rw [h1]
  exact hpow _ x hx

theorem smul_mem_of_gens
    {S : Set Pt} {gA gB : Rgrp} (hgen : Subgroup.closure {gA, gB} = ⊤)
    (hA : ∀ x ∈ S, gA • x ∈ S) (hB : ∀ x ∈ S, gB • x ∈ S) (g : Rgrp) : ∀ x ∈ S, g • x ∈ S := by
  have hg : g ∈ Subgroup.closure {gA, gB} := by rw [hgen]; exact Subgroup.mem_top g
  refine Subgroup.closure_induction (p := fun g _ => ∀ x ∈ S, g • x ∈ S) ?_ ?_ ?_ ?_ hg
  · rintro g (rfl | rfl)
    exacts [hA, hB]
  · intro x hx
    simpa using hx
  · intro g h _ _ hg hh x hx
    rw [mul_smul]
    exact hg _ (hh x hx)
  · intro g _ hg
    exact inv_smul_mem hg

theorem glMat_stdA :
    glMat stdA.1 = toMat nativeAB.1 := glMat_genA

theorem glMat_stdB :
    glMat stdB.1 = toMat nativeAB.2 := glMat_genB

open Matrix in
theorem ncard_of_facts
    {MA MB : Matrix (Fin 78) (Fin 78) K} {gA gB : Rgrp} (hA : glMat gA.1 = MA)
    (hB : glMat gB.1 = MB) (hgen : Subgroup.closure {gA, gB} = ⊤) {n : ℕ} {pts : ℕ → Pt}
    {dep : ℕ → ℕ} (hinj : ∀ i < n, ∀ j < n, pts i = pts j → i = j)
    (he : ∃ r < n, pts r = Pi.single 7 1) (hcA : ∀ i < n, ∃ j < n, pts j = MA *ᵥ pts i)
    (hcB : ∀ i < n, ∃ j < n, pts j = MB *ᵥ pts i) (h0 : ∀ i < n, dep i = 0 → pts i = Pi.single 7 1)
    (hs : ∀ i < n, 0 < dep i → ∃ j < n, dep j < dep i ∧
      (pts i = MA *ᵥ pts j ∨ pts i = MB *ᵥ pts j ∨ pts j = MB *ᵥ pts i)) :
    rootOrbit.ncard = n := by
  have sA : ∀ x, gA • x = MA *ᵥ x := fun x => by rw [smul_def, hA]
  have sB : ∀ x, gB • x = MB *ᵥ x := fun x => by rw [smul_def, hB]
  have hmem : ∀ d, ∀ i < n, dep i = d → pts i ∈ rootOrbit := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro i hi hd
      rcases Nat.eq_zero_or_pos (dep i) with h | h
      · rw [h0 i hi h]
        exact MulAction.mem_orbit_self _
      · obtain ⟨j, hj, hlt, e⟩ := hs i hi h
        have hjm := ih (dep j) (hd ▸ hlt) j hj rfl
        rcases e with e | e | e
        · rw [e, ← sA]
          exact (smul_mem_rootOrbit_iff gA _).2 hjm
        · rw [e, ← sB]
          exact (smul_mem_rootOrbit_iff gB _).2 hjm
        · rw [e, ← sB] at hjm
          exact (smul_mem_rootOrbit_iff gB _).1 hjm
  set S : Set Pt := {x | ∃ i < n, pts i = x} with hSdef
  have hSA : ∀ x ∈ S, gA • x ∈ S := by
    rintro x ⟨i, hi, rfl⟩
    obtain ⟨j, hj, e⟩ := hcA i hi
    exact ⟨j, hj, by rw [e, sA]⟩
  have hSB : ∀ x ∈ S, gB • x ∈ S := by
    rintro x ⟨i, hi, rfl⟩
    obtain ⟨j, hj, e⟩ := hcB i hi
    exact ⟨j, hj, by rw [e, sB]⟩
  have hS := smul_mem_of_gens hgen hSA hSB
  obtain ⟨r, hr, hre⟩ := he
  have he7 : Cert.e7 ∈ S := ⟨r, hr, hre⟩
  have hrange : rootOrbit = (fun i : Fin n => pts i) '' Set.univ := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      obtain ⟨i, hi, e⟩ := hS g _ he7
      exact ⟨⟨i, hi⟩, Set.mem_univ _, e⟩
    · rintro ⟨⟨i, hi⟩, -, rfl⟩
      exact hmem _ i hi rfl
  have hinj' : Function.Injective (fun i : Fin n => pts i) :=
    fun i j h => Fin.ext (hinj i i.2 j j.2 h)
  rw [hrange, Set.ncard_image_of_injective _ hinj', Set.ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_fin]

@[expose] noncomputable def rootFinset :
    Finset Pt := (Set.toFinite rootOrbit).toFinset

theorem mem_rootFinset
    {x : Pt} : x ∈ rootFinset ↔ x ∈ rootOrbit :=
  Set.Finite.mem_toFinset _

noncomputable instance :
    MulAction Rgrp rootOrbit where
  smul g x := ⟨g • x.1, (smul_mem_rootOrbit_iff g x.1).2 x.2⟩
  one_smul x := Subtype.ext (one_smul Rgrp x.1)
  mul_smul g h x := Subtype.ext (mul_smul g h x.1)

theorem coe_smul_rootOrbit
    (g : Rgrp) (x : rootOrbit) : ((g • x : rootOrbit) : Pt) = g • (x : Pt) :=
  rfl

instance :
    MulAction.IsPretransitive Rgrp rootOrbit where
  exists_smul_eq x y := by
    obtain ⟨g, hg⟩ := x.2
    obtain ⟨h, hh⟩ := y.2
    refine ⟨h * g⁻¹, Subtype.ext ?_⟩
    rw [coe_smul_rootOrbit, mul_smul]
    change h • g⁻¹ • (x : Pt) = y
    have : g⁻¹ • (x : Pt) = e7 := by
      rw [← hg]
      exact inv_smul_smul g _
    rw [this]
    exact hh

end CFSG.Monster.Existence.StdOdd.Cert
