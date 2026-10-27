module

public import CFSG.Quasithin.EmptyFaithful.Gold14610LiftMaps
public import CFSG.Quasithin.EmptyFaithful.Gold14610Props

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace Gold14610

variable {G : Type} [Group G] [Finite G] {I K : Subgroup G}

theorem centralExt3_imgMod3 (hKI : K ≤ I) (hsub : IsSubnormal K I)
    (hsyl : IsSylowTwoOf (Open.pCore 2 ↥I) (CFSG.pPrimeCore 3 ↥I))
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (hB : CFSG.IsQuasisimple ↥(imgMod3 I K)) :
    CentralExt3 (↥K ⧸ CFSG.pCore 2 ↥K) ↥(imgMod3 I K) := by
  have hnorm : (CFSG.pCore 2 ↥K).Normal := CFSG.pCore_normal
  let p : (↥K ⧸ CFSG.pCore 2 ↥K) →* ↥(imgMod3 I K) :=
    QuotientGroup.lift (CFSG.pCore 2 ↥K) (toImg hKI) (pCore_le_ker_toImg hKI hsub)
  have hpk : ∀ k : ↥K, p (QuotientGroup.mk k) = toImg hKI k := fun k => rfl
  have hp : Function.Surjective p := by
    intro b
    obtain ⟨k, rfl⟩ := toImg_surjective hKI b
    exact ⟨QuotientGroup.mk k, hpk k⟩
  have hnt : Nontrivial ↥(imgMod3 I K) := CFSG.LocalCores.isQuasisimple_nontrivial hB
  have hX : ∀ a ∈ p.ker,
      (∃ m : ℕ, Odd m ∧ a ^ m = 1) ∧ a ^ Nat.card (CFSG.pPrimeCore 3 ↥I) = 1 := by
    intro a ha
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective a
    have hk : k ∈ (toImg hKI).ker := by
      rw [MonoidHom.mem_ker, ← hpk]
      exact MonoidHom.mem_ker.mp ha
    have hkN := (mem_ker_toImg hKI k).mp hk
    obtain ⟨m, hm, hkm⟩ := exists_odd_pow_mem_pCore_K hKI hsyl ((toD_eq_one_iff hKI k).mpr hkN)
    refine ⟨⟨m, hm, ?_⟩, ?_⟩
    · rw [← QuotientGroup.mk_pow]
      exact (QuotientGroup.eq_one_iff _).mpr hkm
    · rw [← QuotientGroup.mk_pow]
      have h1 : (⟨(k : G), hKI k.2⟩ : ↥I) ^ Nat.card (CFSG.pPrimeCore 3 ↥I) = 1 := by
        have := pow_card_eq_one' (G := ↥(CFSG.pPrimeCore 3 ↥I)) (x := ⟨_, hkN⟩)
        exact congrArg Subtype.val this
      have h2 : k ^ Nat.card (CFSG.pPrimeCore 3 ↥I) = 1 := by
        apply Subtype.ext
        have := congrArg Subtype.val h1
        simpa using this
      rw [h2]
      exact QuotientGroup.mk_one _
  refine ⟨p.ker, MonoidHom.normal_ker p, ?_, ?_, ?_,
    ⟨QuotientGroup.quotientKerEquivOfSurjective p hp⟩⟩
  · rcases CFSG.LocalCores.quasisimple_normal_subgroups hq (MonoidHom.normal_ker p) with h | h
    · exfalso
      obtain ⟨b, hb⟩ : ∃ b : ↥(imgMod3 I K), b ≠ 1 := exists_ne 1
      obtain ⟨a, rfl⟩ := hp b
      have : a ∈ p.ker := by rw [h]; trivial
      exact hb (MonoidHom.mem_ker.mp this)
    · exact h
  · intro hd
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥p.ker) 2 hd
    obtain ⟨m, hm, ham⟩ := (hX a a.2).1
    have hdvd : orderOf (a : ↥K ⧸ CFSG.pCore 2 ↥K) ∣ m := orderOf_dvd_of_pow_eq_one ham
    rw [Subgroup.orderOf_coe, ha] at hdvd
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr hdvd)
  · refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun hd => ?_)
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥p.ker) 3 hd
    have hdvd : orderOf (a : ↥K ⧸ CFSG.pCore 2 ↥K) ∣ Nat.card (CFSG.pPrimeCore 3 ↥I) :=
      orderOf_dvd_of_pow_eq_one (hX a a.2).2
    rw [Subgroup.orderOf_coe, ha] at hdvd
    have hc := CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥I)
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hc hdvd

end Gold14610

end CFSG.Quasithin
