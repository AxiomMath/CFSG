module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowONSevenComm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowONLineMinus
public import CFSG.RankThree.PartOne.KS.ONPointwise

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.HardMathSupport.Dickson.I271 CFSG.ONSchreier

theorem on_exists_inv_of_fix_on7W_zero
    {α : MulAut Pv} (hα2 : α * α = 1) (hα1 : α ≠ 1) (hαx : α (on7W 0) = on7W 0) :
    ∃ z : Pv, IsHeisCenter7 z ∧ α z = z⁻¹ := by
  have h7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rcases sevenLine_fix_or_exists_conj_inv (on7_sevenLine 0) (by norm_num) hα2 hαx with
    hfix | hinv
  · exfalso
    apply hα1
    have hC : ∀ g : Pv,
        (g : Equiv.Perm (Fin N)) ∈ CFSG.RankThree.Native.onSevenC 0 → α g = g := by
      intro g hg
      refine hfix g ?_
      have hR0 : on7R 0 = 0 := rfl
      rw [mem_centralizer_on7W_iff, hR0]
      exact hg
    have h7pow : α ^ 7 = 1 := CFSG.RankThree.PartOne.ONPw.onPointwiseSeven_holds α hC
    have h2 : α ^ 2 = 1 := by rw [pow_two, hα2]
    have hαeq : α = 1 := by
      have h : α ^ 7 = α := by
        rw [show 7 = 2 * 3 + 1 by norm_num, pow_add, pow_mul, h2, one_pow, one_mul, pow_one]
      rw [h7pow] at h
      exact h.symm
    exact hαeq
  · obtain ⟨f, hf, hfz⟩ :=
      hinv (on7W 1) (on7W_mem_F0 1) (on7W_not_mem_zpowers 1 (by decide))
    have hcard : Nat.card (Subgroup.centralizer ({on7W 1} : Set Pv)) = 7 ^ 3 * 4 :=
      card_centralizer_on7W 1
    have hdvd : 2 ∣ Nat.card (Subgroup.centralizer ({on7W 1} : Set Pv)) := by
      rw [hcard]
      norm_num
    obtain ⟨u, hu⟩ :=
      exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.centralizer ({on7W 1} : Set Pv)))
        2 (hp := ⟨by norm_num⟩) hdvd
    have hu2 : (u : Pv) * (u : Pv) = 1 := by
      have h : u ^ 2 = 1 := by rw [← orderOf_dvd_iff_pow_eq_one, hu]
      simpa [pow_two] using congrArg Subtype.val h
    have hu1 : (u : Pv) ≠ 1 := by
      intro h
      have h' : u = 1 := Subtype.ext h
      rw [h', orderOf_one] at hu
      omega
    have huy : (u : Pv) * on7W 1 = on7W 1 * (u : Pv) :=
      Subgroup.mem_centralizer_singleton_iff.mp u.2
    have hz : IsHeisCenter7 (on7W 1) :=
      on_isHeisCenter7_of_comm_involution (on7W_pow_seven 1) (on7W_ne_one 1) hu2 hu1 huy
    exact ⟨f * on7W 1 * f⁻¹, hz.conj f, hfz⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
