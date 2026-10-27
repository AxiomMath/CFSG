module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2LocD

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
  CFSG.QuasithinUnique.Tight CFSG.QuasithinUnique.BenderBranch
  CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

namespace InspW2

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t d x : G}

theorem Bw_pGroup_of_ctx (h : Ctx T M g A t d x) : IsPGroup 2 ↥(Bw T d x) := by
  have hBC : Bw T d x ≤ Cw T d x := inf_le_left
  have hdvd : Nat.card ↥(Bw T d x) ∣ 2 ^ 7 * 3 := by
    have := Subgroup.card_dvd_of_le hBC
    rwa [card_Cw_eq h] at this
  have h3 : ¬ 3 ∣ Nat.card ↥(Bw T d x) := by
    intro hdv
    obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Bw T d x)) 3 hdv
    have hbC : (b : G) ∈ Cw T d x := hBC b.2
    have hodd : Odd (orderOf (b : G)) := by
      rw [Subgroup.orderOf_coe, hb]; decide
    have hbK : (b : G) ∈ K0 T d x :=
      ⟨mem_oTwoUpper_of_odd hbC.1 hodd, hbC.2⟩
    have hcent : ∀ k : ↥(K0 T d x), k * (⟨(b : G), hbK⟩ : ↥(K0 T d x)) =
        (⟨(b : G), hbK⟩ : ↥(K0 T d x)) * k := fun k =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp b.2.2 (k : G) k.2)
    have h4 := z4StarSL23_central_pow_four h.hO hcent
    have h4' : (b : G) ^ 4 = 1 := congrArg Subtype.val h4
    have := orderOf_dvd_of_pow_eq_one h4'
    rw [Subgroup.orderOf_coe, hb] at this
    omega
  have hcop : Nat.Coprime (Nat.card ↥(Bw T d x)) 3 :=
    (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3))
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hcop.dvd_of_dvd_mul_right hdvd)
  exact IsPGroup.of_card hm

end InspW2

end S143

end CFSG.Quasithin
