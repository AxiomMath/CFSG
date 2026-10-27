module

public import CFSG.Quasithin.Vol2.Ch11SecO6B
public import CFSG.Quasithin.Vol2.Ch11SecGTAut
public import CFSG.Quasithin.Vol2.Ch11SecE43Out

public section

namespace CFSG.Quasithin.Vol2.Ch11.O6

open CFSG.Open CFSG.Blueprint

theorem mk_mem_oddCore_of_mem {G : Type} [Group G] {K : Subgroup G} {g : G} (hgK : g ∈ K)
    (hg : g ∈ oTwoTwoPrime K) :
    ((⟨g, hgK⟩ : ↥K) : SecG.Bar.KBar K) ∈ CFSG.oddCore (SecG.Bar.KBar K) := by
  obtain ⟨z, hz, hzg⟩ := hg
  have e : z = ⟨g, hgK⟩ := Subtype.ext hzg
  rw [← e]
  exact hz

end CFSG.Quasithin.Vol2.Ch11.O6

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13


theorem factCase1Comm_holds : FactCase1Comm := by
  intro G _ _ K n hl h1 hperf r x hr hx hrK ⟨k, hk⟩ y hy
  have hD := O6.case1Data_kBar hl h1
  have hX := SecG.Bar.commutator_top_eq_top hperf
  obtain ⟨hCF, hprimes, q, hq, hq5, ψ, hψ, hker⟩ := hD.struct
  have : Fact q.Prime := ⟨hq⟩
  set rN : ↥(Subgroup.normalizer (K : Set G)) := ⟨r, hr⟩
  set xN : ↥(Subgroup.normalizer (K : Set G)) := ⟨x, hx⟩
  set α := SecG.Bar.aut K rN
  set γ := SecG.Bar.aut K xN
  set β := α * γ * α⁻¹ * γ⁻¹ with hβdef
  have hβ : SecG.Bar.aut K (rN * xN * rN⁻¹ * xN⁻¹) = β := by
    simp only [hβdef, α, γ, map_mul, map_inv]
  have hαF : ∀ z : SecG.Bar.KBar K, z⁻¹ * α z ∈ CFSG.fittingSubgroup (SecG.Bar.KBar K) := by
    intro z
    obtain ⟨⟨y', hy'⟩, rfl⟩ := QuotientGroup.mk_surjective z
    rw [← O6.oddCore_eq hD]
    have h2 := hrK y'⁻¹ (K.inv_mem hy')
    have h3 : y'⁻¹ * (r * y' * r⁻¹) ∈ K :=
      K.mul_mem (K.inv_mem hy') ((Subgroup.mem_normalizer_iff.mp hr y').mp hy')
    have h4 : y'⁻¹ * (r * y' * r⁻¹) ∈ oTwoTwoPrime K := by
      have e : y'⁻¹ * (r * y' * r⁻¹) = (r * y'⁻¹ * r⁻¹ * y'⁻¹⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ h2
    have h5 := O6.mk_mem_oddCore_of_mem h3 h4
    convert h5 using 1
    rw [SecG.Bar.aut_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    rfl
  have hβe : β ^ 2 ^ k = 1 := by
    rw [← hβ, ← map_pow]
    have hc : (rN * xN * rN⁻¹ * xN⁻¹) ^ 2 ^ k = 1 := Subtype.ext hk
    rw [hc, map_one]
  have hfixP : ∀ p : (Nat.card (SecG.Bar.KBar K)).primeFactors, ∀ d ∈ CFSG.pCore (p : ℕ)
      (SecG.Bar.KBar K), β d = d := by
    intro p d hd
    have hpp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
    have : Fact (p : ℕ).Prime := ⟨hpp⟩
    by_cases hpF : (p : ℕ) ∣ Nat.card (CFSG.fittingSubgroup (SecG.Bar.KBar K))
    · obtain ⟨m, hm⟩ := O6.actsScalar_of_comm (p : ℕ) (hD.rank p hpp hpF)
        (fun f hf => O6.fitting_acts_triv (p : ℕ) hf)
        (O6.exists_not_triv (p : ℕ) hD hpF (Or.inl hX)) hαF
      have hp2 : (p : ℕ) ≠ 2 := by have := hprimes p hpp hpF; omega
      exact O6.fix_of_actsScalar_one (p : ℕ) hp2 hβe (O6.actsScalar_comm (p : ℕ) hm γ) d hd
    · have hbot : CFSG.pCore (p : ℕ) (SecG.Bar.KBar K) = ⊥ := by
        obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp
          (CFSG.pCore_isPGroup (p := (p : ℕ)) (G := SecG.Bar.KBar K))
        have hdvd : Nat.card (CFSG.pCore (p : ℕ) (SecG.Bar.KBar K)) ∣
            Nat.card (CFSG.fittingSubgroup (SecG.Bar.KBar K)) :=
          Subgroup.card_dvd_of_le (CFSG.pCore_le_fitting _ _)
        rcases j with _ | j
        · exact Subgroup.eq_bot_of_card_eq _ (by rw [hj, pow_zero])
        · exact absurd ((dvd_pow_self (p : ℕ) (Nat.succ_ne_zero j)).trans (hj ▸ hdvd)) hpF
      rw [hbot, Subgroup.mem_bot] at hd
      rw [hd, map_one]
  have hfixF : ∀ f ∈ CFSG.fittingSubgroup (SecG.Bar.KBar K), β f = f := by
    let Fix : Subgroup (SecG.Bar.KBar K) :=
      { carrier := {d | β d = d}
        one_mem' := map_one β
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_ofPred_eq, map_mul] at ha hb ⊢
          rw [ha, hb]
        inv_mem' := fun {a} ha => by
          simp only [Set.mem_ofPred_eq, map_inv] at ha ⊢
          rw [ha] }
    intro f hf
    rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore] at hf
    exact (iSup_le fun p d hd => hfixP p d hd : _ ≤ Fix) hf
  have hFodd : Odd (Nat.card (CFSG.fittingSubgroup (SecG.Bar.KBar K))) := by
    rw [Nat.odd_iff]
    by_contra h
    have := hprimes 2 Nat.prime_two (Nat.dvd_of_mod_eq_zero (by omega))
    omega
  have hβ1 : β = 1 := SecG.AutFit.eq_one_of_commFitting hX inferInstance hCF hFodd
    (k := ZMod q) (by rw [Nat.card_zmod]; omega) ψ hψ hker hβe fun f hf => by
      rw [hfixF f hf, mul_inv_cancel]
      exact Subgroup.one_mem _
  obtain ⟨z, hz, hzc⟩ := SecG.Bar.comm_mem_of_aut_eq_one (hβ.trans hβ1) y hy
  have h1 := (SecE.mk_eq_one_iff K z).mp ((QuotientGroup.eq_one_iff z).mpr hz)
  rw [show (z : G) = r * x * r⁻¹ * x⁻¹ * y * (r * x * r⁻¹ * x⁻¹)⁻¹ * y⁻¹ from hzc] at h1
  exact h1

end CFSG.Quasithin.Vol2.Ch11.SecE
