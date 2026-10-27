module

public import CFSG.RankThree.PartOne.CTP.UnitaryEdge
public import CFSG.RankThree.PartOne.CTP.PhanBridge
public import CFSG.RankThree.PartOne.CTP.PhanFour
public import CFSG.RankThree.PartOne.CTP.ExtA

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.LieType.Universal.Unitary (SUid)
open scoped MatrixGroups

theorem extPhan : ExtPhan := by
  intro G _ _ n f p K E hn hf hp hp3 hpq hE hgen hK2 hcomm hadj htor
  have hq : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hp2 : p ≠ 2 := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hfd : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f (GaloisField 2 (2 * f)) :=
    ⟨Nat.prime_two, by omega, by rw [hF, ← pow_mul, mul_comm]⟩
  have hcomm' : ∀ i j : Fin n, (i : ℕ) + 1 < j → ∀ x ∈ K i, ∀ y ∈ K j, x * y = y * x := by
    intro i j hij x hx y hy
    have hne : i ≠ j := by
      intro h
      subst h
      omega
    have hna : ¬ chainAdj i j := by
      rintro (h | h) <;> omega
    exact (Subgroup.mem_centralizer_iff.mp ((hcomm i j hne hna).1 hx) y hy).symm
  have hW : CFSG.ClassicalInvolution.Phan.WeakPhanA (GaloisField 2 (2 * f)) 2 f n K
      (fun i j => K i ⊔ K j) :=
    { iso := fun i => by
        obtain ⟨L, _, _, _, hL, ⟨ρ⟩⟩ := exists_sl2_equiv_of_model (hK2 i)
        obtain ⟨e⟩ := exists_suid_two_equiv_sl hF hL
        exact ⟨e.trans ρ⟩
      join := fun i j _ => rfl
      comm := hcomm'
      pair := by
        intro i j hij
        have hne : i ≠ j := by
          intro h
          subst h
          omega
        obtain ⟨θ₀, hsurj, hker₀⟩ :=
          exists_su3_surj_of_centrallyUThree hF (hadj i j (Or.inl hij.symm))
        obtain ⟨Li, _, _, _, hLi, ⟨ρi⟩⟩ := exists_sl2_equiv_of_model (hK2 i)
        obtain ⟨Lj, _, _, _, hLj, ⟨ρj⟩⟩ := exists_sl2_equiv_of_model (hK2 j)
        let θ : SUid (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 3 →* G :=
          (K i ⊔ K j).subtype.comp θ₀
        have hrange : θ.range = K i ⊔ K j := by
          rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
            Subgroup.range_subtype]
        have hker : θ.ker ≤ Subgroup.center
            (SUid (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 3) := by
          intro x hx
          exact hker₀ (Subtype.ext hx)
        have hE' : EdgeTorus p E (K i) (K j) :=
          ⟨(htor.1 i).1, (htor.1 i).2, (htor.1 j).1, (htor.1 j).2, htor.2 i j hne⟩
        obtain ⟨c, hc1, hc2⟩ := unitary_edge_standardPair hfd hq hp hp2 hpq θ hker hE'
          hrange.symm hLi hLj ρi ρj
        exact ⟨θ, c, hrange, hker, Or.inl ⟨hc1, hc2⟩⟩
      gen := hgen }
  obtain ⟨θ, hθs, hθk⟩ := weakPhan_recognition_of_four_le (GaloisField 2 (2 * f)) 2 f hF hq hn hW
  exact statedClassicalModel_psu_of_surjective hF hq (by omega) θ hθs hθk

end CFSG.RankThree.PartOne.CTP
