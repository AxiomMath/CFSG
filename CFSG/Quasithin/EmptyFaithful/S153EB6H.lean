module

public import CFSG.Quasithin.EmptyFaithful.S153EB6C
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

namespace S153EB6

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

section Fix3

variable {V : Type} [CommGroup V]

theorem exists_three_fix_of_mt {G : Subgroup (MulAut V)} (hmt : G64.ModuleType G ⊤)
    (hbig : 8 ≤ Nat.card V) (p : V) : ∃ g ∈ G, orderOf g = 3 ∧ g p = p := by
  rcases hmt with ⟨n, hn2, hn5, K, instK, instKF, hK, hreal⟩ | ⟨n, hn5, hn8, hreal⟩ |
    ⟨n, hn, hreal⟩
  · have hc := card_of_realizes_nat n G hreal
    rw [hK] at hc
    have hn3 : 3 ≤ n := by
      by_contra hlt
      have : 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : Nat.card V ≤ 4 := by rw [hc]; simpa using this
      omega
    obtain ⟨π, hπ⟩ := hreal
    exact exists_order_three_fix (FFModel.nat (StatedSL n K)) G π hπ
      (fun (m : Multiplicative (Fin n → K)) _ => by
        obtain ⟨γ, hγ3, hγm, m', hm'⟩ := natSL_fix (K := K) (by simpa using hK) n hn3 m
        refine ⟨γ, hγ3, ?_, m', Subgroup.mem_top _, fun hmem => hm' ?_⟩
        · show natAct (StatedSL n K) γ m * m⁻¹ ∈ (⊥ : Subgroup (Multiplicative (Fin n → K)))
          rw [hγm, mul_inv_cancel]
          exact one_mem _
        · exact mul_inv_eq_one.1 (Subgroup.mem_bot.1 hmem)) p
  · obtain ⟨π, hπ⟩ := hreal
    exact exists_order_three_fix (FFModel.symDn n) G π hπ
      (fun (m : G6.PermMod n) _ => by
        obtain ⟨γ, hγ3, hγm, m', hm'c, hm'⟩ := perm_cyc n hn5 m
        refine ⟨γ, hγ3, ?_, m', hm'c, fun hmem => hm' (Subgroup.mem_inf.1 hmem).1⟩
        show G6.permAct n γ m * m⁻¹ ∈ Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n
        rw [hγm, show m * m⁻¹ = 1 from mul_inv_cancel m]
        exact one_mem _) p
  · have hn5 : 5 ≤ n := by omega
    obtain ⟨π, hπ⟩ := hreal
    exact exists_order_three_fix (G64.symCoreModel n) G π hπ
      (fun (m : G6.PermMod n) _ => by
        obtain ⟨γ, hγ3, hγm, m', hm'c, hm'⟩ := perm_cyc n hn5 m
        refine ⟨γ, hγ3, ?_, m', hm'c, fun hmem => hm' ?_⟩
        · show G6.permAct n γ m * m⁻¹ ∈ (⊥ : Subgroup (G6.PermMod n))
          rw [hγm, show m * m⁻¹ = 1 from mul_inv_cancel m]
          exact one_mem _
        · have h1 : G6.permAct n γ m' * m'⁻¹ = 1 := Subgroup.mem_bot.1 hmem
          rw [h1]
          exact one_mem _) p

end Fix3

end S153EB6

end CFSG.Quasithin
