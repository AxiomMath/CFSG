module

public import CFSG.Quasithin.Background.A3Structure312Facts
public import CFSG.Quasithin.Background.DicksonPerfectSL2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Quasithin.Dickson CFSG.Quasithin.A1c
open scoped MatrixGroups commutatorElement

theorem a312SL2Fact : A312SL2Fact := by
  intro p hp hp3 X _ _ hX S hS B hB hBtop
  obtain ⟨f⟩ := hX
  have hfinj : Function.Injective f.toMonoidHom := f.injective
  have : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by
    by_contra h
    have h4 : p = 4 := by omega
    rw [h4] at hp
    exact absurd hp (by norm_num)
  have hBne : B ≠ ⊥ := hB.1
  have hBperf : ⁅B, B⁆ = B := hB.2.1
  have hBsub : IsSubnormal B (B ⊔ S) := hB.2.2.1
  let B' : Subgroup (SL(2, ZMod p)) := B.map f.toMonoidHom
  have hB'perf : ⁅B', B'⁆ = B' := by
    simp only [B']
    rw [← Subgroup.map_commutator, hBperf]
  have hB'ne : B' ≠ ⊥ := fun h =>
    hBne ((Subgroup.map_eq_bot_iff_of_injective B f.injective).1 h)
  have hB'top : B' ≠ ⊤ := fun h => hBtop (by
    apply Subgroup.map_injective hfinj
    rw [Subgroup.map_top_of_surjective _ f.surjective]
    exact h)
  rcases perfect_subgroup_sl2_prime hp5 hB'perf hB'ne with h | ⟨⟨eB⟩, h5mod, -, -, hmax⟩
  · exact absurd h hB'top
  · refine ⟨⟨(B.equivMapOfInjective f.toMonoidHom f.injective).trans eB⟩, h5mod, ?_⟩
    have hsup : B ⊔ S ≠ ⊤ := by
      intro htop
      rw [htop] at hBsub
      have hlt : B < ⊤ := lt_top_iff_ne_top.2 hBtop
      obtain ⟨P, hPlt, hPn, hBP⟩ := A3.subnormal_exists_normal_of_lt hBsub hlt
      have hPnorm : P.Normal :=
        Subgroup.normalizer_eq_top_iff.1
          (top_le_iff.1 ((Subgroup.normal_subgroupOf_iff_le_normalizer le_top).1 hPn))
      have hPm : (P.map f.toMonoidHom).Normal := hPnorm.map f.toMonoidHom f.surjective
      rcases normal_le_center_or_eq_top hp5 (P.map f.toMonoidHom) with hc | htop'
      ·
        have hperf : Group.IsPerfect B' := Subgroup.isPerfect_iff.2 hB'perf
        have : IsMulCommutative B' := ⟨⟨fun a b =>
          Subtype.ext (Subgroup.mem_center_iff.1
            (hc (Subgroup.map_mono hBP a.2)) b).symm⟩⟩
        exact hB'ne (Subgroup.eq_bot_of_subsingleton B')
      · exact hPlt.ne (Subgroup.map_injective hfinj (by
          rw [htop', Subgroup.map_top_of_surjective _ f.surjective]))
    have hSB : S ≤ B := by
      rcases hmax ((B ⊔ S).map f.toMonoidHom) (Subgroup.map_mono le_sup_left) with h | h
      · intro s hs
        have : f s ∈ B' := h ▸ Subgroup.mem_map_of_mem f.toMonoidHom ((le_sup_right : S ≤ B ⊔ S) hs)
        obtain ⟨b, hb, hbs⟩ := this
        have : b = s := f.injective hbs
        exact this ▸ hb
      · exact absurd (Subgroup.map_injective hfinj (by
          rw [h, Subgroup.map_top_of_surjective _ f.surjective])) hsup
    have hcardB : Nat.card B = 120 := by
      rw [Nat.card_congr ((B.equivMapOfInjective f.toMonoidHom f.injective).trans eB).toEquiv,
        card_sl2_five]
    have h2fact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hS.2.1
    have hdvd : Nat.card S ∣ 120 := hcardB ▸ Subgroup.card_dvd_of_le hSB
    have hle8 : Nat.card S ≤ 8 := by
      by_contra hgt
      push Not at hgt
      have hn4 : 4 ≤ n := by
        by_contra h4
        push Not at h4
        have : 2 ^ n ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have h16 : 2 ^ 4 ∣ Nat.card S := hn ▸ pow_dvd_pow 2 hn4
      have := h16.trans hdvd
      norm_num at this
    have hodd : ¬ 2 ∣ S.index := by
      have h := hS.2.2
      change ¬ 2 ∣ S.relIndex ⊤ at h
      rwa [Subgroup.relIndex_top_right] at h
    have hcardX : Nat.card X = p * (p ^ 2 - 1) := by
      rw [Nat.card_congr f.toEquiv, CFSG.GorensteinWalter.sl2_card_formula, Nat.card_zmod]
    have hmul : Nat.card S * S.index = p * (p ^ 2 - 1) := by
      rw [Subgroup.card_mul_index, hcardX]
    have hpodd : p % 2 = 1 := by
      have h : ¬ 2 ∣ p := fun h => by
        rcases hp.eq_one_or_self_of_dvd 2 h with h | h <;> omega
      omega
    by_contra hmod
    have h18 : p % 8 = 1 ∨ p % 8 = 7 := by omega
    have hp16 : p % 16 = 1 ∨ p % 16 = 7 ∨ p % 16 = 9 ∨ p % 16 = 15 := by omega
    have hsq : p ^ 2 % 16 = 1 := by
      rcases hp16 with h | h | h | h <;> simp [pow_two, Nat.mul_mod, h]
    have h16 : 16 ∣ p * (p ^ 2 - 1) := Dvd.dvd.mul_left (by omega) _
    have hcop : Nat.Coprime 16 S.index := by
      have h2 : Nat.Coprime 2 S.index := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd
      simpa using h2.pow_left 4
    have h16S : 16 ∣ Nat.card S := hcop.dvd_of_dvd_mul_right (hmul ▸ h16)
    have := Nat.le_of_dvd Nat.card_pos h16S
    omega

end CFSG.Quasithin
