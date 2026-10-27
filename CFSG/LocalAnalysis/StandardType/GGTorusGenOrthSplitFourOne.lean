module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenOrthSplitFourLift
public import CFSG.HardMathSupport.Seitz.Proving.SL2PrimeOrder
import TauCeti.GroupTheory.ExponentPrime

public section

namespace CFSG.StandardType.OrthTorusGen

open Module Multiplicative QuadraticMap Polynomial
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.LocalAnalysis.ComponentInitial CFSG.StandardType.LayerCores CFSG.StandardType.LayerFacts
open CFSG.StandardType.SevOm
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {E : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

theorem exists_mul_of_mem_sup_pow_eq_one {G : Type*} [Group G] {T₁ T₂ : Subgroup G}
    (hinf : T₁ ⊓ T₂ = ⊥) (hcomm : ∀ a ∈ T₁, ∀ b ∈ T₂, a * b = b * a)
    {y : G} (hy : y ∈ T₁ ⊔ T₂) (hyp : y ^ p = 1) :
    ∃ a ∈ T₁, ∃ b ∈ T₂, y = a * b ∧ a ^ p = 1 ∧ b ^ p = 1 ∧
      a * y = y * a ∧ b * y = y * b := by
  obtain ⟨q, hq⟩ := MonoidHom.mem_range.mp
    (show y ∈ (CFSG.RankThree.PartTwo.Sec14.Ronan148J.commProdHom hcomm).range from by
      rw [CFSG.RankThree.PartTwo.Sec14.Ronan148J.commProdHom_range hcomm]
      exact hy)
  have hq' : (q.1 : G) * (q.2 : G) = y := by
    rw [← hq, CFSG.RankThree.PartTwo.Sec14.Ronan148J.commProdHom_apply]
  set a : G := (q.1 : G) with haeq
  set b : G := (q.2 : G) with hbeq
  have ha : a ∈ T₁ := by rw [haeq]; exact q.1.2
  have hb : b ∈ T₂ := by rw [hbeq]; exact q.2.2
  have hab : y = a * b := by rw [haeq, hbeq]; exact hq'.symm
  have hcomm_ay : a * y = y * a := by
    rw [hab, mul_assoc, hcomm a ha b hb]
  have hcomm_by : b * y = y * b := by
    rw [hab, ← mul_assoc, hcomm a ha b hb]
  have hcy : Commute a b := hcomm a ha b hb
  have habp : a ^ p * b ^ p = 1 := by
    rw [← hcy.mul_pow, ← hab, hyp]
  have hap : a ^ p = 1 := by
    have hmem : a ^ p ∈ T₁ ⊓ T₂ := by
      refine Subgroup.mem_inf.mpr ⟨T₁.pow_mem ha p, ?_⟩
      rw [eq_inv_of_mul_eq_one_left habp]
      exact T₂.inv_mem (T₂.pow_mem hb p)
    rw [hinf] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hbp : b ^ p = 1 := by
    have h := habp
    rw [hap, one_mul] at h
    exact h
  exact ⟨a, ha, b, hb, hab, hap, hbp, hcomm_ay, hcomm_by⟩

theorem mem_or_mem_of_forall_mem_zpowers {G : Type*} [Group G] (hp : p.Prime)
    {T₁ T₂ : Subgroup G} (hinf : T₁ ⊓ T₂ = ⊥) (hcomm : ∀ a ∈ T₁, ∀ b ∈ T₂, a * b = b * a)
    {y : G} (hy : y ∈ T₁ ⊔ T₂) (hyp : y ^ p = 1)
    (hz : ∀ h, (h ∈ T₁ ∨ h ∈ T₂) → h * y = y * h → h ^ p = 1 → h ∈ Subgroup.zpowers y) :
    y ∈ T₁ ∨ y ∈ T₂ := by
  obtain ⟨a, ha, b, hb, hab, hap, _, hcomm_ay, _⟩ :=
    exists_mul_of_mem_sup_pow_eq_one hinf hcomm hy hyp
  have hamem : a ∈ Subgroup.zpowers y := hz a (Or.inl ha) hcomm_ay hap
  by_cases ha1 : a = 1
  · refine Or.inr ?_
    rw [hab, ha1, one_mul]
    exact hb
  · refine Or.inl (Subgroup.zpowers_le.mpr ha ?_)
    rw [TauCeti.zpowers_eq_zpowers_of_mem_zpowers hp hyp ha1 hamem]
    exact Subgroup.mem_zpowers y

omit [CharP K 2] in
theorem dvd_card_sq_sub_one (hp : p.Prime) (F : SevOm.Frame Q p E r)
    (hU : ∀ j, finrank K (F.U j) = 2) (k : Fin r) : p ∣ Nat.card K ^ 2 - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 := F.dvd_card_sub_one k
  have h2 : Nat.card (F.U k) = Nat.card K ^ finrank K (F.U k) :=
    Module.natCard_eq_pow_finrank
  rw [hU k] at h2
  rwa [h2] at h1

omit [CharP K 2] in
theorem splitFour_false_of_mem_factor (hp : p.Prime) (hEΩ : E ≤ orthDerived Q)
    (F : SevOm.Frame Q p E r) (hU : ∀ j, finrank K (F.U j) = 2)
    (hmax : ∀ g ∈ orthDerived Q, (∀ c ∈ E, g * c = c * g) → g ^ p = 1 → g ∈ E)
    {s : Multiplicative (Fin r → ZMod p)} (hx : OddOrderIsometry Q p (F.ι s)) {k : Fin r}
    (hothers : ∀ j, j ≠ k → toAdd s j ≠ 0)
    (hτ : F.ι (frameDelta k) ∈ supportedBlock Q (F.ι s) (X - 1))
    {T T' : Subgroup (fixedSpace (F.ι s) ≃ₗ[K] fixedSpace (F.ι s))}
    (hT'D : T' ≤ orthDerived (Q.comp (fixedSpace (F.ι s)).subtype)) (hinf : T ⊓ T' = ⊥)
    (hcommT : ∀ x ∈ T, ∀ y ∈ T', x * y = y * x)
    {ψ' : SL(2, K) →* (fixedSpace (F.ι s) ≃ₗ[K] fixedSpace (F.ι s))}
    (hψ' : Function.Injective ψ') (hr' : ψ'.range = T')
    (hτT : fixRho hx ⟨F.ι (frameDelta k), hτ⟩ ∈ T) : False := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨a, ha⟩ :=
    CFSG.HardMathSupport.Seitz.Proving.exists_orderOf_eq_prime_SL2 hp
      (dvd_card_sq_sub_one hp F hU k)
  set h : fixedSpace (F.ι s) ≃ₗ[K] fixedSpace (F.ι s) := ψ' a with hh
  have horder : orderOf h = p := by
    rw [hh, orderOf_injective ψ' hψ' a, ha]
  have hhT' : h ∈ T' := by
    rw [← hr']
    exact MonoidHom.mem_range.mpr ⟨a, hh.symm⟩
  have hhD : h ∈ orthDerived (Q.comp (fixedSpace (F.ι s)).subtype) := hT'D hhT'
  have hhτ : h * fixRho hx ⟨F.ι (frameDelta k), hτ⟩ =
      fixRho hx ⟨F.ι (frameDelta k), hτ⟩ * h :=
    (hcommT _ hτT h hhT').symm
  have hhp : h ^ p = 1 := by
    have hpow := pow_orderOf_eq_one h
    rwa [horder] at hpow
  have hmem := mem_zpowers_of_commute_fixRho hEΩ F hmax hx hothers hτ hhD hhτ hhp
  have hbot : h ∈ (⊥ : Subgroup (fixedSpace (F.ι s) ≃ₗ[K] fixedSpace (F.ι s))) := by
    rw [← hinf]
    exact Subgroup.mem_inf.mpr ⟨Subgroup.zpowers_le.mpr hτT hmem, hhT'⟩
  have h1 : h = 1 := Subgroup.mem_bot.mp hbot
  have h2 : p = 1 := by
    rw [← horder, h1, orderOf_one]
  exact hp.ne_one h2

omit [Finite K] [CharP K 2] in
theorem fixRho_frameDelta_mem_orthDerived_and_pow_eq_one (hp : p.Prime) (hp2 : p ≠ 2)
    (F : SevOm.Frame Q p E r) {s : Multiplicative (Fin r → ZMod p)}
    (hx : OddOrderIsometry Q p (F.ι s)) {k : Fin r}
    (hτ : F.ι (frameDelta k) ∈ supportedBlock Q (F.ι s) (X - 1))
    (hoddO : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace (F.ι s)).subtype),
      Odd (orderOf g) → g ∈ orthDerived (Q.comp (fixedSpace (F.ι s)).subtype)) :
    fixRho hx ⟨F.ι (frameDelta k), hτ⟩ ∈ orthDerived (Q.comp (fixedSpace (F.ι s)).subtype) ∧
      fixRho hx ⟨F.ι (frameDelta k), hτ⟩ ^ p = 1 := by
  have hyO : fixRho hx ⟨F.ι (frameDelta k), hτ⟩ ∈
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace (F.ι s)).subtype) := by
    rw [← range_fixRho hx]
    exact MonoidHom.mem_range.mpr ⟨⟨F.ι (frameDelta k), hτ⟩, rfl⟩
  have hyp : fixRho hx ⟨F.ι (frameDelta k), hτ⟩ ^ p = 1 := by
    rw [← map_pow]
    have h1 : (⟨F.ι (frameDelta k), hτ⟩ :
        ↥(supportedBlock Q (F.ι s) (X - 1))) ^ p = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one, F.pow_p])
    rw [h1, map_one]
  exact ⟨hoddO _ hyO ((hp.odd_of_ne_two hp2).of_dvd_nat (orderOf_dvd_of_pow_eq_one hyp)), hyp⟩

theorem splitFour_one_coord_false (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hEΩ : E ≤ orthDerived Q) (F : SevOm.Frame Q p E r)
    (hU : ∀ j, finrank K (F.U j) = 2)
    (hmax : ∀ g ∈ orthDerived Q, (∀ c ∈ E, g * c = c * g) → g ^ p = 1 → g ∈ E)
    (s : Multiplicative (Fin r → ZMod p)) (hx : OddOrderIsometry Q p (F.ι s)) {k : Fin r}
    (hk : toAdd s k = 0) (hothers : ∀ j, j ≠ k → toAdd s j ≠ 0)
    {T₁ T₂ : Subgroup (fixedSpace (F.ι s) ≃ₗ[K] fixedSpace (F.ι s))}
    (hsup : orthDerived (Q.comp (fixedSpace (F.ι s)).subtype) = T₁ ⊔ T₂)
    (hcommT : ∀ x ∈ T₁, ∀ y ∈ T₂, x * y = y * x)
    {ψ₁ ψ₂ : SL(2, K) →* (fixedSpace (F.ι s) ≃ₗ[K] fixedSpace (F.ι s))}
    (hψ₁ : Function.Injective ψ₁) (hr₁ : ψ₁.range = T₁)
    (hψ₂ : Function.Injective ψ₂) (hr₂ : ψ₂.range = T₂)
    (hoddO : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace (F.ι s)).subtype),
      Odd (orderOf g) → g ∈ orthDerived (Q.comp (fixedSpace (F.ι s)).subtype)) :
    False := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hinf : T₁ ⊓ T₂ = ⊥ := splitFour_inf_eq_bot hcommT hψ₁ hr₁
  have hτ : F.ι (frameDelta k) ∈ supportedBlock Q (F.ι s) (X - 1) :=
    frameDelta_mem_supportedBlock hQ hp hp2 hEΩ F s hk
  obtain ⟨hyD, hyp⟩ := fixRho_frameDelta_mem_orthDerived_and_pow_eq_one hp hp2 F hx hτ hoddO
  set y : fixedSpace (F.ι s) ≃ₗ[K] fixedSpace (F.ι s) :=
    fixRho hx ⟨F.ι (frameDelta k), hτ⟩
  have hy12 : y ∈ T₁ ∨ y ∈ T₂ := by
    refine mem_or_mem_of_forall_mem_zpowers hp hinf hcommT ?_ hyp ?_
    · rw [← hsup]
      exact hyD
    · intro h hmem hcomm hhp
      have hD : h ∈ orthDerived (Q.comp (fixedSpace (F.ι s)).subtype) := by
        rw [hsup]
        exact hmem.elim (fun h1 => Subgroup.mem_sup_left h1)
          (fun h2 => Subgroup.mem_sup_right h2)
      exact mem_zpowers_of_commute_fixRho hEΩ F hmax hx hothers hτ hD hcomm hhp
  rcases hy12 with hy1 | hy2
  · refine splitFour_false_of_mem_factor hp hEΩ F hU hmax hx hothers hτ ?_ hinf hcommT
      hψ₂ hr₂ hy1
    rw [hsup]
    exact le_sup_right
  · refine splitFour_false_of_mem_factor hp hEΩ F hU hmax hx hothers hτ ?_ ?_ ?_ hψ₁ hr₁ hy2
    · rw [hsup]
      exact le_sup_left
    · rw [inf_comm]
      exact hinf
    · intro x hx2 y' hy1
      exact (hcommT y' hy1 x hx2).symm

end CFSG.StandardType.OrthTorusGen
