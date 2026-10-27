module

public import CFSG.Quasithin.H13.NQCoreP134X27Borel
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieSp4Transport

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem noX27Simple_psp4Even (n : ℕ) :
    NoX27Simple fun (X : Type) [Group X] => StatedClassicalModel X .PSp 2 2 n := by
  intro A _ _ L P T hcfg h27 hL
  obtain ⟨⟨-, hn1, -, hne⟩, K, _, _, hK, ⟨e⟩⟩ := hL
  have hn : 2 ≤ n := by
    by_contra h'
    have : n = 1 := by omega
    subst this
    exact hne rfl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have := hcfg.normal
  have hU := OddConfig.isSylowTwoOf_inf hcfg
  obtain ⟨-, hab, -⟩ := Psp4.normalizes_of_mulEquiv_odd hK4
    (e.trans (Lin2.Five.projEquiv K).symm) hU hcfg.le (p := 3) (a := 3) (by norm_num)
    (Or.inr rfl) (by rw [h27]; norm_num) hcfg.exp (OddConfig.mul_inf hcfg)
  exact hcfg.false_of_comm_x27 h27 hab

theorem facts134X27_psp4Even :
    ∀ f : ℕ, 2 ≤ f →
    NoX27ConfigQ fun (X : Type) [Group X] => StatedClassicalModel X .PSp 2 2 f := fun f _ =>
  noX27ConfigQ_of_noCover (fun _ _ _ _ e h => CFSG.SectionRank.statedClassicalModel_of_mulEquiv
    e.symm h) (noX27Simple_psp4Even f) fun X _ _ hX h3 h => by
      have : Group.IsPerfect X := hX.1
      have hodd : Odd (Nat.card (Subgroup.center X)) := by
        rw [h3]
        decide
      have hZ := (CFSG.SectionRank.EvenCover.even_symplectic_odd_cover_catalog_step hX hodd h).1
      rw [hZ, Subgroup.card_bot] at h3
      omega

end CFSG.Quasithin.H13.NQCore
