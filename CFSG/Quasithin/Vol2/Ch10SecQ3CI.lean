module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CH
public import CFSG.Quasithin.Vol2.Ch10SecQ3CBc
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.EmptyFaithful.Setting
public import CFSG.Quasithin.Vol2.Ch10SecB3FactsE
public import CFSG.Quasithin.Vol2.Ch11SecBDerived
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Quasithin.Vol2.Ch1Prop121

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_borel_of_e22Cases {H T X K : Subgroup G} (hn1 : 1 < E1.nParam H)
    (hcases : E2.E22Cases H T X K) :
    ∃ n : ℕ, 2 ≤ n ∧ (E2.IsBenderOf n ↥(E2.star X H K) ∨ IsPSL 3 2 n ↥(E2.star X H K) ∨
        IsPSp4 2 n ↥(E2.star X H K)) ∧
      E2.IsBorelIn (E2.star X H K) (E2.star X H (X ⊓ K)) ∧ E1.nParam H = n := by
  dsimp only [E2.E22Cases] at hcases
  rcases hcases with ⟨-, -, -, -, -, h1⟩ | ⟨-, -, h2⟩
  · rcases h1 with ⟨n, hn, htype, hBor, hnH⟩ | ⟨_, _, _, _, _, _, hnH⟩
    · exact ⟨n, hn, Or.inl ⟨hn, htype.elim Or.inl fun h => Or.inr (Or.inl h)⟩, hBor, hnH⟩
    · exact absurd hn1 (by rw [hnH]; exact lt_irrefl 1)
  · rcases h2 with ⟨n, hBen, hBor, hnH⟩ | ⟨n, -, htype, -, hBor, hnH⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hnH⟩ | ⟨_, _, _, _, _, hnH⟩
    · exact ⟨n, hBen.1, Or.inl hBen, hBor, hnH⟩
    · have hn2 : 1 < n := by
        rw [hnH] at hn1
        exact_mod_cast hn1
      refine ⟨n, hn2, ?_, hBor, hnH⟩
      rcases htype with h | h
      · exact Or.inr (Or.inl h)
      · right; right
        rw [E2.IsSp4Prime] at h
        split_ifs at h with h1
        · omega
        · exact h
    · exact absurd hn1 (by rw [hnH]; exact lt_irrefl 1)
    · exact absurd hn1 (by rw [hnH]; exact lt_irrefl 1)

omit [Finite G] in
theorem isSylowTwoOf_top_subgroupOf {K S : Subgroup G} (hS : IsSylowTwoOf S K) :
    IsSylowTwoOf (S.subgroupOf K) (⊤ : Subgroup K) := by
  refine ⟨le_top, hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm, ?_⟩
  rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
  exact hS.2.2

omit [Finite G] in
theorem coe_mem_normalizer {K S : Subgroup G} (hSK : S ≤ K) {d : ↥K}
    (hd : d ∈ Subgroup.normalizer ((S.subgroupOf K : Subgroup K) : Set K)) :
    (d : G) ∈ Subgroup.normalizer (S : Set G) := by
  refine Subgroup.mem_normalizer_iff.mpr fun w => ⟨fun hw => ?_, fun hw => ?_⟩
  · have h := (Subgroup.mem_normalizer_iff.mp hd ⟨w, hSK hw⟩).mp hw
    exact h
  · have hwK : w ∈ K := by
      have h1 : (d : G) * w * (d : G)⁻¹ ∈ K := hSK hw
      have h2 := K.mul_mem (K.mul_mem (K.inv_mem d.2) h1) d.2
      simpa [mul_assoc] using h2
    exact (Subgroup.mem_normalizer_iff.mp hd ⟨w, hwK⟩).mpr hw

end C11AmS

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13 C11AmS

theorem fact10_2_3Cartan_of (hE22 : E2.E22Statement) (hDHB : Ch11.SecB.DerivedHallBorel)
    (hBC : FactBorelCartan) : Fact10_2_3Cartan := by
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
  obtain ⟨⟨K, -, -, -, hcases⟩, -⟩ := hE22 G H T X hmin
    (sqtkGroup_of_pCoreOf_ne_bot hK hs hnab hH.1.2) hns
  obtain ⟨n, hn2, htype, ⟨S, hS, hBor⟩, hnH⟩ := exists_borel_of_e22Cases hn1 hcases
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
