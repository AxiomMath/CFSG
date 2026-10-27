
module

public import CFSG.Sporadic.Co2Schreier.ThirdChainBase
public import CFSG.Sporadic.Co2Schreier.Enum
public import CFSG.Sporadic.Co2Schreier.ChainCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.Arrays
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.Co2Schreier.TextCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.Text
public import CFSG.Sporadic.Co2Schreier.ThirdCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.WitCheck
public meta import CFSG.Sporadic.Co2Schreier.SylowCheckBase
public meta import CFSG.Sporadic.Co2Schreier.CoreCheckBase
public meta import CFSG.Sporadic.Co2Cert.FaithfulCheck
public import CFSG.Sporadic.Co2Cert.CheckInputs
public import CFSG.Sporadic.Co2Cert.OrderCheckInputs

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert

@[expose] def locU : Equiv.Perm (Fin 2300) := sTuple.getD 8 1 * sTuple.getD 0 1

theorem locU_mem_S : locU ∈ locS :=
  locS.mul_mem (Subgroup.subset_closure (getD_mem (by rw [sTuple_length]; norm_num)))
    (Subgroup.subset_closure (getD_mem (by rw [sTuple_length]; norm_num)))

theorem locU_mem : locU ∈ co2P := locS_le_P locU_mem_S

@[expose] def locH3 : Subgroup (Equiv.Perm (Fin 2300)) := co2P ⊓ Subgroup.centralizer {locU}

theorem mem_locH3 {h : Equiv.Perm (Fin 2300)} : h ∈ locH3 ↔ h ∈ co2P ∧ locU * h = h * locU := by
  rw [locH3, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2.symm⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2.symm⟩

theorem rep_apply {t : Array ℕ} {g : Equiv.Perm (Fin 2300)} (ht : Rep 2300 t g) (x : Fin 2300) :
    t[(x : ℕ)]! = (g x : ℕ) := ht x

open scoped Classical in
@[irreducible, expose] def cosetH (j : ℕ) (p : Equiv.Perm (Fin 2300)) :
    Finset (Equiv.Perm (Fin 2300)) :=
  Finset.univ.filter fun h => h ∈ locH3 ∧ p⁻¹ * h ∈ stabB j

theorem mem_cosetH {j : ℕ} {p h : Equiv.Perm (Fin 2300)} :
    h ∈ cosetH j p ↔ h ∈ locH3 ∧ p⁻¹ * h ∈ stabB j := by
  classical
  unfold cosetH
  simp

theorem fix_of_comm {u h q : Equiv.Perm (Fin 2300)} {b : Fin 2300} (hc : u * h = h * u)
    (hu : u b = b) (hq : h b = q b) : u (q b) = q b := by
  rw [← hq]
  have := congrArg (fun g : Equiv.Perm (Fin 2300) => g b) hc
  simp only [Equiv.Perm.mul_apply, hu] at this
  exact this

theorem foldl_cond_sum (n : ℕ) (c : ℕ → Prop) [DecidablePred c] (g : ℕ → ℕ) :
    (List.range n).foldl (fun acc k => if c k then acc else acc + g k) 0 =
      ∑ k ∈ Finset.range n, if c k then 0 else g k := by
  suffices h : ∀ a : ℕ, (List.range n).foldl (fun acc k => if c k then acc else acc + g k) a =
      a + ∑ k ∈ Finset.range n, if c k then 0 else g k by simpa using h 0
  induction n with
  | zero => intro a; simp
  | succ n ih =>
    intro a
    rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ, List.foldl_cons,
      List.foldl_nil]
    split_ifs <;> omega

end CFSG.Sporadic.Co2Schreier
