module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CI
public import CFSG.Quasithin.Background.E2TwoCCases

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.H13 C11AmS

@[expose] def Fact10_2_3CartanLe : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → InM T M → Subgroup.normalizer (T : Set G) ≤ M → IsHStar T M H →
    1 < E1.nParam H →
      ∃ n : ℕ, E1.nParam H ≤ n ∧ ∀ B : Subgroup G,
        QuasithinUnique.Lin2.IsHallTwoPrimeOf B (H ⊓ M) → ∃ b ∈ B, orderOf b = 2 ^ n - 1

theorem fact10_2_3CartanLe_of (hE22 : E2.E22StatementC) (hDHB : Ch11.SecB.DerivedHallBorel)
    (hBC : FactBorelCartan) : Fact10_2_3CartanLe := by
  intro G _ _ T M H hs hnab hK hT hTM hN hH hn1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := H ⊓ M with hXdef
  have hTH : T ≤ H := hH.1.1
  have hTX : T ≤ X := le_inf hTH hTM.2
  have hTS : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo hT hTH
  obtain ⟨P, hP⟩ := exists_sylow_of_quasithinIsSylowTwo hT
  have hU : IsUniqueMaxOver H T X := by
    have := IsHStar.isUniqueMaxOver P (hP ▸ hH) (hP ▸ hTM.2)
    rwa [hP] at this
  have hmin : MinParabolic H T X := ⟨hTS, hH.not_le_normalizer hN, hU⟩
  have hns : ¬ Group.IsSolvable ↥H := fun hsol =>
    absurd hn1 (not_lt.mpr (E1.solvable_nParam_le_one hsol))
  obtain ⟨⟨K, -, -, -, hcases⟩, -⟩ := hE22.exists_cases hmin
    (sqtkGroup_of_pCoreOf_ne_bot hK hs hnab hH.1.2) hns
  obtain ⟨n, hn2, htype, ⟨S, hS, hBor⟩, hnH⟩ := E2.exists_borel_of_e22CasesC hn1 hcases
  refine ⟨n, hnH, fun B hB => ?_⟩
  obtain ⟨d, hdN, hdo⟩ := hBC _ n hn2 htype _ (isSylowTwoOf_top_subgroupOf hS)
  have hdM : (d : E2.StarQuot X H) ∈ E2.star X H (X ⊓ K) := by
    rw [hBor]
    exact ⟨d.2, coe_mem_normalizer hS.1 hdN⟩
  obtain ⟨⟨x, hxH⟩, hx, hxe⟩ := hdM
  have hxXK : x ∈ X ⊓ K := hx
  have hdvd : 2 ^ n - 1 ∣ orderOf x := by
    rw [← hdo, ← Subgroup.orderOf_coe d, ← hxe]
    have h := orderOf_map_dvd (QuotientGroup.mk' ((kerIn X H).subgroupOf H)) (⟨x, hxH⟩ : ↥H)
    rwa [← Subgroup.orderOf_coe] at h
  obtain ⟨a, r, hr, hxar⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  have hyo : orderOf (x ^ 2 ^ a) = r := by
    rw [orderOf_pow_of_dvd (by positivity) (by rw [hxar]; exact dvd_mul_right _ _), hxar,
      Nat.mul_div_cancel_left _ (by positivity)]
  have hodd : Odd (2 ^ n - 1) := Nat.Even.sub_odd (Nat.one_le_two_pow) (Nat.even_pow.mpr
    ⟨even_two, by omega⟩) odd_one
  have hdvr : 2 ^ n - 1 ∣ r := by
    rw [hxar] at hdvd
    exact (Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)).dvd_of_dvd_mul_left hdvd
  obtain ⟨B₀, hB₀, -, hTQ⟩ := hDHB G T M H hs hnab hK hT hTM hN hH hn1
  obtain ⟨b, hb, hbdvd⟩ := exists_mem_orderOf_dvd (isSylowTwoOf_of_quasithinIsSylowTwo hT hTX)
    hB₀ hTQ hB (X.pow_mem hxXK.1 _) (by rw [hyo]; exact hr)
  rw [hyo] at hbdvd
  have hfin : 2 ^ n - 1 ∣ orderOf b := hdvr.trans hbdvd
  exact ⟨b ^ (orderOf b / (2 ^ n - 1)), B.pow_mem hb _,
    orderOf_pow_orderOf_div (orderOf_pos b).ne' hfin⟩

end CFSG.Quasithin.Vol2.Ch10.SecB
