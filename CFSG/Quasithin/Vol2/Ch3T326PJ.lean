module

public import CFSG.Quasithin.Vol2.Ch3T326PH

public section

namespace CFSG.Quasithin.H13.T326

open CFSG.Quasithin CFSG.Quasithin.SmithD321 CFSG.Quasithin.SmithD39Two CFSG.Quasithin.Z391
  CFSG.Quasithin.SmithD391 CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Open

variable {W : Type} [CommGroup W] [Finite W]

theorem oTwoUpper_eq_of {G : Type*} [Group G] {C : Subgroup G} [Finite ↥C] {a b : ℕ}
    (hcard : Nat.card ↥C = 2 ^ a * 5 ^ b) (S : Sylow 5 ↥C) (hSn : (S : Subgroup ↥C).Normal) :
    oTwoUpper C = (S : Subgroup ↥C).map C.subtype := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨hxC, hodd⟩
    have hord : orderOf (⟨x, hxC⟩ : ↥C) = orderOf x := Subgroup.orderOf_mk x hxC
    have hdvd : orderOf (⟨x, hxC⟩ : ↥C) ∣ 2 ^ a * 5 ^ b :=
      hcard ▸ orderOf_dvd_natCard _
    have hcop : Nat.Coprime (orderOf (⟨x, hxC⟩ : ↥C)) (2 ^ a) :=
      Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 (hord ▸ hodd))
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).1
      (hcop.dvd_of_dvd_mul_left hdvd)
    have hP : IsPGroup 5 ↥(Subgroup.zpowers (⟨x, hxC⟩ : ↥C)) :=
      IsPGroup.of_card (by rw [Nat.card_zpowers, hk])
    obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
    have hQS : Q = S :=
      @Subsingleton.elim _ (@Unique.instSubsingleton _ (Sylow.unique_of_normal S hSn)) Q S
    subst hQS
    exact ⟨⟨x, hxC⟩, hQ (Subgroup.mem_zpowers _), rfl⟩
  · rintro _ ⟨s, hs, rfl⟩
    refine mem_oTwoUpper_of_odd s.2 ?_
    obtain ⟨k, hk⟩ := S.2 ⟨s, hs⟩
    have h1 : (s : G) ^ 5 ^ k = 1 := by
      have h2 := congrArg (fun z : ↥(S : Subgroup ↥C) => (((z : ↥C) : G))) hk
      simpa using h2
    exact Odd.of_dvd_nat (Odd.pow (by decide)) (orderOf_dvd_of_pow_eq_one h1)

namespace O2Sit

variable {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
  (h : O2Sit M Mp T L V t)
include h

theorem oTwoUpper_eq (S : Sylow 5 ↥(M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)))) :
    oTwoUpper (M ⊓ Subgroup.centralizer (Mp : Set (MulAut W))) =
      (S : Subgroup ↥(M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)))).map
        (M ⊓ Subgroup.centralizer (Mp : Set (MulAut W))).subtype := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine oTwoUpper_eq_of h.card_cent_eq S ?_
  rw [h.sylow_eq_pCore S]
  exact CFSG.pCore_normal

end O2Sit

end CFSG.Quasithin.H13.T326
