module

public import CFSG.LocalAnalysis.UniquenessCase.UC22L3Frame
public import CFSG.LocalAnalysis.UniquenessCase.UC22L3LinFieldsC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.L3Lin

open Matrix Subgroup CFSG.GH74.KGroups.L3Eps CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem two_ne_zero_of_charP {p : ℕ} [hp : Fact p.Prime] [CharP F p] (hp2 : p ≠ 2) :
    (2 : F) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1
    ((CharP.cast_eq_zero_iff F p 2).1 h'))

theorem three_ne_zero_of_charP {p : ℕ} [hp : Fact p.Prime] [CharP F p] (hp3 : p ≠ 3) :
    (3 : F) ≠ 0 := by
  intro h
  have h' : ((3 : ℕ) : F) = 0 := by exact_mod_cast h
  exact hp3 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).1
    ((CharP.cast_eq_zero_iff F p 3).1 h'))

@[expose] noncomputable def linFrame [Finite F] {p : ℕ} [hp : Fact p.Prime] [CharP F p]
    (hp5 : 5 ≤ p) (hcard : Nat.card F = p)
    (hY : CFSG.Open.StatedClassicalModel (projectiveSL 3 F) .PSL 3 p 1) :
    L3Frame (MulAut (projectiveSL 3 F)) p F :=
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_charP hp2
  have h3 : (3 : F) ≠ 0 := three_ne_zero_of_charP (by omega)
  have h4 : 4 ≤ Nat.card F := by omega
  have hσ : ∀ σ : F ≃+* F, σ = 1 := ringEquiv_eq_one_of_card_prime hcard
  have hodd : Odd (Nat.card F) := by rw [hcard]; exact hp.out.odd_of_ne_two hp2
  { I := (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range
    P := (conjAut 3 F).range
    e := eA F
    r := rA F
    Kb := KS F
    Zb := ZS F
    ρ := rho h2
    I_normal := inn_normal_Y
    P_normal := inndiag_normal_Y
    I_le_P := inn_le_inndiag_Y
    mul_mem_of_not_mem := fun _ _ hg hh => mul_mem_of_not_mem_lin hσ hg hh
    mem_I_of_two := fun _ hg _ hn => mem_inn_of_two_pow hg hn
    e_mem := ⟨_, rfl⟩
    r_mem := ⟨_, rfl⟩
    e_pow_four := eA_pow_four
    r_sq := rA_sq
    r_e := rA_eA
    e_sq_ne := eA_sq_ne_one h2
    isCyclic_cent := isCyclic_cent_lin h2
    isPGroup_D8 := isPGroup_D8_lin
    Kb_le := KS_le_CS
    conj_mem_Kb := fun _ hg _ hx => conj_mem_KS_lin h2 h4 hg hx
    mem_Zb := fun _ => mem_ZS_iff
    isCyclic_Zb := isCyclic_ZS h2
    eq_one_of_mem_Kb_Zb := fun _ hxK hxZ hodd' => eq_one_of_mem_KS_ZS h2 hxK hxZ hodd'
    ρ_eq_one := fun x => rho_eq_one_iff h2 x
    eight_dvd := eight_dvd_card_range_rho h2 hodd
    ρ_ne := fun he hr => rho_ne_lin h2 he hr
    isPGroup_of_comm := fun he hr g h1 h2' =>
      ⟨1, by rw [pow_one]; exact sq_eq_one_of_comm_rho h2 he hr g h1 h2'⟩
    not_unip := fun u _ hρ h1 h2' => not_unip_lin hp2 h2 u hρ h1 h2'
    mem_Kb_of_inv := fun x w hx hw => mem_KS_of_inv h2 x w hx hw
    comm_of_comm_Kb := fun _ hx hx1 hxc _ hg hgx => comm_of_comm_KS hx hx1 hxc hg hgx
    comm_of_comm_Zb := fun _ hd hd1 _ _ hg hgd => comm_of_comm_ZS h2 hd hd1 hg hgd
    not_inv_Zb := fun _ hd hd1 hdo _ hg => not_inv_ZS h2 hd hd1 hdo hg
    comm_of_abelian := fun _ _ hAB hBP hBab h3B _ h6 he hr =>
      comm_of_abelian_lin h2 h3 hAB hBP hBab h3B h6 he hr
    exists_conj_Kb := fun _ hv => exists_conj_KS_lin hσ hv
    comm_of_coprime_six := fun _ _ hy6 _ hR hyR => comm_of_coprime_six_lin hp2 hY hy6 hR hyR }

theorem linFrame_I [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p] (hp5 : 5 ≤ p)
    (hcard : Nat.card F = p) (hY : CFSG.Open.StatedClassicalModel (projectiveSL 3 F) .PSL 3 p 1) :
    (linFrame hp5 hcard hY).I =
      (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range :=
  rfl

theorem linFrame_Kb [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p] (hp5 : 5 ≤ p)
    (hcard : Nat.card F = p) (hY : CFSG.Open.StatedClassicalModel (projectiveSL 3 F) .PSL 3 p 1) :
    (linFrame hp5 hcard hY).Kb = KS F :=
  rfl

end CFSG.LocalAnalysis.UniquenessCase.UC22.L3Lin
