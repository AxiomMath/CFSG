module

public import CFSG.Quasithin.AppendixH.H9.VectorStabilizer.Action
public import CFSG.Quasithin.AppendixH.H9.VectorStabilizer.Model
public import CFSG.Quasithin.AppendixH.H9.VectorStabilizer.Hyperplane

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH.VectorStabilizer

open CFSG.Quasithin CFSG.Open

variable {m : ℕ}

private theorem mem_K2_iff (u : PairN (m + 1)) :
    u ∈ V2n (m + 1) ⊓ perpN (m + 1) (Subgroup.zpowers (pairVec (ez m) 0)) ↔
      ∃ b : Fin (m + 1) → ZMod 2, b 0 = 0 ∧ u = pairVec 0 b := by
  rw [mem_V2n_perpN_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨Multiplicative.toAdd u.2, h2, ?_⟩
    exact Prod.ext h1 rfl
  · rintro ⟨b, hb, rfl⟩
    exact ⟨rfl, hb⟩

private theorem aut_mem_bot {V : Type*} [CommGroup V] (g : MulAut V) {z : V}
    (hz : z ∈ (⊥ : Subgroup V)) : g z ∈ (⊥ : Subgroup V) := by
  rw [Subgroup.mem_bot] at hz ⊢
  rw [hz]
  exact map_one g

private def betaHom (m : ℕ) :
    ↥(V2n (m + 1) ⊓ perpN (m + 1) (Subgroup.zpowers (pairVec (ez m) 0))) →*
      Multiplicative (Fin m → ZMod 2) where
  toFun u := Multiplicative.ofAdd fun i : Fin m => Multiplicative.toAdd (u : PairN (m + 1)).2 i.succ
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext i
    simp
  map_mul' u u' := by
    apply Multiplicative.toAdd.injective
    funext i
    simp

private theorem betaHom_apply (u : ↥(V2n (m + 1) ⊓ perpN (m + 1) (Subgroup.zpowers (pairVec (ez m) 0))))
    (b : Fin (m + 1) → ZMod 2) (hu : (u : PairN (m + 1)) = pairVec 0 b) :
    betaHom m u = Multiplicative.ofAdd fun i : Fin m => b i.succ := by
  show Multiplicative.ofAdd (fun i : Fin m => Multiplicative.toAdd (u : PairN (m + 1)).2 i.succ) = _
  rw [hu]
  rfl

private theorem natHom_apply_ofAdd (D : GL (Fin m) (ZMod 2)) (w : Fin m → ZMod 2) :
    natHom m (ZMod 2) D (Multiplicative.ofAdd w) =
      Multiplicative.ofAdd ((D : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ w) := rfl

private theorem pairActN_pairVec_zero (A : GL (Fin (m + 1)) (ZMod 2)) (b : Fin (m + 1) → ZMod 2) :
    pairActN (m + 1) A (pairVec 0 b) =
      pairVec 0 (((dualGLn (m + 1) A : GL (Fin (m + 1)) (ZMod 2)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) *ᵥ b) := by
  rw [pairActN_pairVec, Matrix.mulVec_zero]

private theorem betaHom_comp {A : GL (Fin (m + 1)) (ZMod 2)} (hA : A ∈ stabGL m)
    (u u' : ↥(V2n (m + 1) ⊓ perpN (m + 1) (Subgroup.zpowers (pairVec (ez m) 0))))
    (h : (u' : PairN (m + 1)) = pairActN (m + 1) A (u : PairN (m + 1))) :
    betaHom m u' = natHom m (ZMod 2) (dualGLn m (blockHom m ⟨A, hA⟩)) (betaHom m u) := by
  obtain ⟨b, hb0, hb⟩ := (mem_K2_iff _).mp u.2
  rw [betaHom_apply u b hb, natHom_apply_ofAdd]
  have h' : (u' : PairN (m + 1)) = pairVec 0 (((dualGLn (m + 1) A : GL (Fin (m + 1)) (ZMod 2)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) *ᵥ b) := by
    rw [h, hb, pairActN_pairVec_zero]
  rw [betaHom_apply u' _ h']
  congr 1
  funext i
  rw [dualGLn_stabGL_mulVec_succ hA b i, hb0]
  simp

theorem inducesOn_Cv (m : ℕ) :
    InducesOn (Lg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) 0)))
      (V2n (m + 1) ⊓ perpN (m + 1) (Subgroup.zpowers (pairVec (ez m) 0))) ⊥
      (Multiplicative (Fin m → ZMod 2)) (natSub m (ZMod 2) ⊤) := by
  refine ⟨bot_le, ?_, ?_, betaHom m, ?_, ?_, ?_, ?_⟩
  · intro g hg u hu
    obtain ⟨A, hA, rfl⟩ := mem_Lg_inf_centSub_iff.mp hg
    obtain ⟨b, hb0, rfl⟩ := (mem_K2_iff _).mp hu
    refine (mem_K2_iff _).mpr ⟨_, ?_, pairActN_pairVec_zero A b⟩
    rw [dualGLn_stabGL_mulVec_zero hA, hb0]
  · intro g hg z hz
    exact aut_mem_bot g hz
  · intro y
    refine ⟨⟨pairVec 0 (Matrix.vecCons 0 (Multiplicative.toAdd y)),
      (mem_K2_iff _).mpr ⟨_, by simp, rfl⟩⟩, ?_⟩
    exact (betaHom_apply _ (Matrix.vecCons 0 (Multiplicative.toAdd y)) rfl).trans (by simp)
  · intro u
    obtain ⟨b, hb0, hb⟩ := (mem_K2_iff _).mp u.2
    have hβ := betaHom_apply u b hb
    constructor
    · intro h
      have h' : Multiplicative.ofAdd (fun i : Fin m => b i.succ) = 1 := hβ.symm.trans h
      have h1 : (fun i : Fin m => b i.succ) = 0 := by simpa using h'
      have hb' : b = 0 := by
        funext i
        induction i using Fin.cases with
        | zero => simpa using hb0
        | succ j => exact congrFun h1 j
      have hu1 : (u : PairN (m + 1)) = 1 := by rw [hb, hb', pairVec_one]
      exact Subgroup.mem_bot.mpr hu1
    · intro h
      have hu1 : (u : PairN (m + 1)) = 1 := Subgroup.mem_bot.mp h
      have hu : u = 1 := Subtype.ext hu1
      exact (congrArg (betaHom m) hu).trans (map_one _)
  · intro g hg
    obtain ⟨A, hA, rfl⟩ := mem_Lg_inf_centSub_iff.mp hg
    refine ⟨natHom m (ZMod 2) (dualGLn m (blockHom m ⟨A, hA⟩)),
      Subgroup.mem_map.mpr ⟨_, Subgroup.mem_top _, rfl⟩, fun u u' h => betaHom_comp hA u u' h⟩
  · intro γ hγ
    obtain ⟨D, -, rfl⟩ := Subgroup.mem_map.mp hγ
    refine ⟨pairActN (m + 1) (leviHom m (dualGLn m D)),
      mem_Lg_inf_centSub_iff.mpr ⟨_, leviHom_mem _, rfl⟩, fun u u' h => ?_⟩
    have := betaHom_comp (leviHom_mem (dualGLn m D)) u u' h
    rwa [blockHom_leviHom, dualGLn_dualGLn] at this

end CFSG.ASVolI.ChH.VectorStabilizer
