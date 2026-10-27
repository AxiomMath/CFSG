module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K326Wreath

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

variable {P : Type*} [Group P] [Finite P] {n : ℕ}

theorem zwr_n_eq_one_of_normal_exp3 (hn : 1 ≤ n) (e : P ≃* ZWr n) {D : Subgroup P}
    (hD : D.Normal) (hexp : ∀ x ∈ D, x ^ 3 = 1) (hnab : ¬ IsMulCommutative D) : n = 1 := by
  have hD' : (D.map e.toMonoidHom).Normal := hD.map e.toMonoidHom e.surjective
  have hnab' : ¬ IsMulCommutative (D.map e.toMonoidHom) := by
    intro h
    apply hnab
    refine ⟨⟨fun x y => Subtype.ext (e.injective ?_)⟩⟩
    have hc := congrArg Subtype.val (h.is_comm.comm
      ⟨e (x : P), Subgroup.mem_map_of_mem e.toMonoidHom x.2⟩
      ⟨e (y : P), Subgroup.mem_map_of_mem e.toMonoidHom y.2⟩)
    simpa only [map_mul, Subgroup.coe_mul] using hc
  have hcomm : commutator (ZWr n) ≤ D.map e.toMonoidHom :=
    commutator_le_of_normal_nonabelian_Zwr hn hD' hnab'
  have helD : el n 1 (-1) 0 0 ∈ D.map e.toMonoidHom :=
    hcomm el_one_neg_one_mem_commutator_Zwr
  obtain ⟨x, hxD, hx⟩ := Subgroup.mem_map.mp helD
  have hx3 : (el n 1 (-1) 0 0) ^ 3 = 1 := by
    rw [← hx, ← map_pow, hexp x hxD, map_one]
  have hpow : el n (3 • (1 : ZMod (3 ^ n))) (3 • (-1)) (3 • (0 : ZMod (3 ^ n))) 0 = 1 := by
    rw [← el_pow_base, hx3]
  have hzero : (3 : ZMod (3 ^ n)) = 0 := by
    rw [← el_zero_zero] at hpow
    have hfirst := congrArg
      (fun w : ZWr n => Multiplicative.toAdd (w.left (Multiplicative.ofAdd 0))) hpow
    simp only [el_left_zero, toAdd_ofAdd] at hfirst
    simpa using hfirst
  have hdvd : 3 ^ n ∣ 3 :=
    (ZMod.natCast_eq_zero_iff 3 (3 ^ n)).mp (by simpa using hzero)
  have hnle : n ≤ 1 :=
    (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).mp (by simpa using hdvd)
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326
