module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2cNbr
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Cal
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Base

public section

namespace CFSG.Quasithin.Fan86.P2c

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
  {F : FanTree Γ G} {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem ballStab_two_all (h71c : Fan71c F L) {c : G} (hc : c ∈ D.calpha) {j : Fin 5}
    (hj : c ∈ ballStab Γ G 2 (D.beta j)) (s : Fin 5) : c ∈ ballStab Γ G 2 (D.beta s) := by
  have hcx : D.x * c = c * D.x :=
    (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2) D.x (Set.mem_singleton _)
  have hconj : (D.x⁻¹)⁻¹ * c * D.x⁻¹ = c := by
    rw [inv_inv, hcx]
    group
  open Fin.NatCast Fin.CommRing in
  have key : ∀ n : ℕ, c ∈ ballStab Γ G 2 (D.beta (j + (n : Fin 5))) := by
    intro n
    induction n with
    | zero => simpa using hj
    | succ n ih =>
      have e : D.beta (j + ((n + 1 : ℕ) : Fin 5)) = D.x⁻¹ • D.beta (j + (n : Fin 5)) := by
        rw [D.hxβ F h71c]
        congr 1
        push_cast
        ring
      rw [e]
      exact mem_ballStab_smul F D.x⁻¹ (by rw [hconj]; exact ih)
  open Fin.NatCast Fin.CommRing in
  have e2 : j + (((s - j).val : ℕ) : Fin 5) = s := by
    rw [Fin.cast_val_eq_self]
    ring
  have := key (s - j).val
  rwa [e2] at this

theorem calpha_mem_zpowers (h7 : Fan7 F L) {c : G} (hc : c ∈ D.calpha) {j : Fin 5}
    (hj : c ∈ ballStab Γ G 2 (D.beta j)) : c ∈ Subgroup.zpowers (L.z α) := by
  obtain ⟨-, -, h71c, -, -, -, -, -, h75⟩ := h7
  have hcα : c • α = α := MulAction.mem_stabilizer_iff.1
    (F.nbrStab_le_stabilizer α (Subgroup.mem_inf.1 hc).1)
  have h3 : c ∈ ballStab Γ G 3 α := by
    refine mem_ballStab_three F hcα fun β hβ => ?_
    obtain ⟨s, rfl⟩ := D.exists_beta_eq F h71c hβ
    exact ballStab_two_all D h71c hc hj s
  obtain ⟨P, -, h4, -⟩ := D.exists_arc8 F h71c (i := 2) (j := 0) (by decide)
  have := (h75 P (by rw [h4]; exact D.val)).1
  rw [h4] at this
  rw [← this]
  exact h3

end CFSG.Quasithin.Fan86.P2c
