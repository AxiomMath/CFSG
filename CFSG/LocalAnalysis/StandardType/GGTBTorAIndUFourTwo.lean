module

public import CFSG.LocalAnalysis.StandardType.GGTorusInducedTransfer
public import CFSG.LocalAnalysis.StandardType.GGTDModelU
public import CFSG.LocalAnalysis.StandardType.GGTDModelAssemble
public import CFSG.LocalAnalysis.StandardType.GGK1ScUni
public import CFSG.LocalAnalysis.StandardType.GGTBTorAIndHolds

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalGroups.UnitaryFlag

theorem ggTDInnerTorus_of_actsDiagU {K : Type} [Field K] {n N : ℕ} {R : Type} [Group R]
    {φ₀ : ↥(unitarySU 2 n K (N + 1)) →* R} (hM₀ : UnitTB.Model φ₀) (hN : 2 ≤ N)
    (hcop : Nat.Coprime (N + 1) (2 ^ n + 1)) (hZ : Subgroup.center R = ⊥)
    (M₀ : GGTDModel K N (2 ^ n + 1) R)
    (hchar : ∀ a : MulAut R, (∃ t, M₀.Act a t) ↔
      ∃ t : Fin (N + 1) → K, LineU.ActsDiagU φ₀ a t) :
    GGTDInnerTorus M₀ := by
  intro a t ha
  obtain ⟨t', ha'⟩ := (hchar a).mp ⟨t, ha⟩
  obtain ⟨D, u, hD, rfl⟩ :=
    exists_eq_conj_diag_of_actsDiagU hM₀.field (by omega) hcop hM₀.surj ha'
  obtain ⟨t'', ht''⟩ := (hchar (MulAut.conj (φ₀ D))).mpr ⟨u, LineU.actsDiagU_conj (φ := φ₀) hD⟩
  obtain ⟨g₀, hg₀⟩ := M₀.surj (φ₀ D)
  rw [← hg₀] at ht''
  obtain ⟨s, z, hz, hs⟩ := M₀.inner_diag g₀ ht''
  rw [hZ, Subgroup.mem_bot] at hz
  refine ⟨s, ?_⟩
  rw [← hg₀, hs, hz, mul_one]

section Certificates


theorem isPGroup_two_ker_unitary {K : Type} [Field K] [Finite K] {n d : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2))
    (hcop : Nat.Coprime d (2 ^ n + 1)) {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤) : IsPGroup 2 ψ.ker := by
  have hZ : IsPGroup 2 (Subgroup.center L') := by
    refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_)
    intro r hr hrd
    by_contra hr2
    have hrd' : ¬ (r ∣ d ∧ r ∣ 2 ^ n + 1) := fun ⟨h1, h2⟩ =>
      hr.one_lt.ne' (Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd h1 h2))
    exact ggCenterPrime_unitary_gcd hK hn hd hdq hr hr2 hrd' L' ψ hψ hker hperf hrd
  exact hZ.to_le hker

theorem ggTorusTorW_unitary_liftTwo_weak {K : Type} [Field K] [Finite K] {n p N : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hN : 3 ≤ N) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hcop : Nat.Coprime (N + 1) (2 ^ n + 1))
    {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin (N + 1)) K (2 ^ n))}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hAe : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin (N + 1)) K (2 ^ n)))
      (LargeEvenGUSet (Fin (N + 1)) K (2 ^ n)),
      ∀ l : L', φ (ψ l) = ψ (a l))
    (hsc : GGTorusSelfCent p A) :
    GGTorusTorData (2 ^ n + 1) N (CartanMatrix.A N) (CoxeterMatrix.A N) L' A := by
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  have hpd : ¬ p ∣ N + 1 := fun h =>
    hp.one_lt.ne' (Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd h hpq))
  have hdq : (N + 1, 2 ^ n) ≠ (3, 2) := fun h => by
    have := congrArg Prod.fst h
    simp only at this
    omega
  have : Finite (LargeEvenProj (LargeEvenSUGroup (Fin (N + 1)) K (2 ^ n))) :=
    Finite.of_surjective ψ hψ
  have hAind : ∀ a ∈ A, ∃ φ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin (N + 1)) K (2 ^ n))),
      ∀ l, φ (ψ l) = ψ (a l) := fun a ha => by
    obtain ⟨x, -, hx⟩ := hAI a ha
    exact ⟨x, hx⟩
  have hEb : IsElemAbelian p (TypeA.inducedSub ψ A) := TypeA.isElemAbelian_inducedSub hψ hAe
  have hEbI : ((TypeA.inducedSub ψ A : Subgroup _) : Set _) ⊆
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin (N + 1)) K (2 ^ n)))
        (LargeEvenGUSet (Fin (N + 1)) K (2 ^ n)) := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := TypeA.mem_inducedSub.mp hx
    obtain ⟨y, hy, hya⟩ := hAI a ha
    rw [TypeA.induced_unique ψ hψ hxa hya]
    exact hy
  have hperfR : commutator (LargeEvenProj (LargeEvenSUGroup (Fin (N + 1)) K (2 ^ n))) = ⊤ := by
    have h1 : (commutator L').map ψ =
        commutator (LargeEvenProj (LargeEvenSUGroup (Fin (N + 1)) K (2 ^ n))) := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective ψ hψ]
    rw [← h1, hperf, Subgroup.map_top_of_surjective ψ hψ]
  obtain ⟨φ₀, hM₀, hEbdiag⟩ :=
    exists_diagModel_PSU_coprime hK hn (by omega) hp hpq hpd hperfR hEb hEbI
  obtain ⟨M₀, hM₀act, hM₀P⟩ := exists_ggTDModel_U hK hn hp hpq hN hM₀
  have hZR : Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin (N + 1)) K (2 ^ n))) = ⊥ :=
    TableBUE.center_proj_eq_bot hK (by omega) hdq
  have hin : GGTDInnerTorus M₀ :=
    ggTDInnerTorus_of_actsDiagU hM₀ (by omega) hcop hZR M₀ hM₀act
  have h2 : IsPGroup 2 ψ.ker := isPGroup_two_ker_unitary hK hn (by omega) hdq hcop hψ hker hperf
  have hm : Odd (2 ^ n + 1) := (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
  obtain ⟨M, hMact, hMP⟩ := exists_ggTDModel_liftTwo M₀ hψ hker h2 hperf hZR hm hin
  have hAT : ∀ a ∈ A, ∃ t, M.Act a t := by
    intro a ha
    obtain ⟨x, -, hx⟩ := hAI a ha
    obtain ⟨t, ht⟩ := (hM₀act x).mpr (hEbdiag x (TypeA.mem_inducedSub.mpr ⟨a, ha, hx⟩))
    exact ⟨t, (hMact a t).mpr ⟨x, ht, hx⟩⟩
  have hEbsc : GGTorusSelfCent p (TypeA.inducedSub ψ A) :=
    ggTorusSelfCent_inducedSub_of_two hψ hker h2 hp hp2 hAind hsc
  obtain ⟨ρb, hρbinj, hρbrange, hρbsw⟩ :=
    exists_permAut_unitary hM₀ hK hp hp2 hpq (by omega) hEb hEbsc hEbdiag
  have hPmR : ∀ σ, MulAut.conj (ψ (M.φ (M.Pm σ))) ∈
      Subgroup.normalizer ((TypeA.inducedSub ψ A : Subgroup _) : Set _) := fun σ => by
    rw [hMP σ, hM₀P σ]
    exact unitDvd_conj_perm_mem_normalizer hM₀ hp hpq (by omega) hEb.2 hEbsc hEbdiag σ⁻¹
  have hN' : ∀ σ, MulAut.conj (M.φ (M.Pm σ)) ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
    fun σ => inducedSub_conj_mem_normalizer hker hperf hAind rfl (hPmR σ)
  set Φ := MulAut.congr (TypeA.inducedSubEquiv hψ hker hperf hAind).symm with hΦ
  refine ggTDtorData_of_model M hp hp2 hpq (by positivity) (by omega) hsc hAT hN'
    (Φ.toMonoidHom.comp ρb) (Φ.injective.comp hρbinj) ?_ fun k => ?_
  · rw [MonoidHom.range_comp, hρbrange]
    exact map_ggAutomizer_inducedSub hψ hker hperf hAind
  · have hsw : (Equiv.swap k.castSucc k.succ)⁻¹ = Equiv.swap k.castSucc k.succ :=
      Equiv.swap_inv _ _
    have hσ : MulAut.conj (φ₀ (LineU.permSU hM₀.field (Equiv.swap k.castSucc k.succ))) ∈
        Subgroup.normalizer ((TypeA.inducedSub ψ A : Subgroup _) : Set _) := by
      have := hPmR (Equiv.swap k.castSucc k.succ)
      rwa [hMP, hM₀P, hsw] at this
    have hψP : ψ (M.φ (M.Pm (Equiv.swap k.castSucc k.succ))) =
        φ₀ (LineU.permSU hM₀.field (Equiv.swap k.castSucc k.succ)) := by
      rw [hMP, hM₀P, hsw]
    change Φ (ρb (Equiv.swap k.castSucc k.succ)) = _
    rw [hρbsw _ hσ]
    have e : ∀ (x : LargeEvenProj (LargeEvenSUGroup (Fin (N + 1)) K (2 ^ n)))
        (hx : MulAut.conj x ∈ Subgroup.normalizer ((TypeA.inducedSub ψ A : Subgroup _) : Set _)),
        x = ψ (M.φ (M.Pm (Equiv.swap k.castSucc k.succ))) →
        Φ (ggConjAut (TypeA.inducedSub ψ A) hx) =
          ggConjAut A (hN' (Equiv.swap k.castSucc k.succ)) := by
      rintro x hx rfl
      exact mulAutCongr_ggConjAut hψ hker hperf hAind _ hx
    exact e _ hσ hψP.symm

theorem ggTorusTorW_unitary_liftTwo {K : Type} [Field K] [Finite K] {n p N : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hN : 3 ≤ N) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hcop : Nat.Coprime (N + 1) (2 ^ n + 1)) :
    GGTorusTorW p (N - 1) (2 ^ n + 1) N (CartanMatrix.A N) (CoxeterMatrix.A N)
      (LargeEvenProj (LargeEvenSUGroup (Fin (N + 1)) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin (N + 1)) K (2 ^ n)))
        (LargeEvenGUSet (Fin (N + 1)) K (2 ^ n))) := by
  intro L' _ _ ψ A hTB
  obtain ⟨hψ, hker, hperf, hAe, hAI, -, -, hsc⟩ := hTB
  exact ggTorusTorW_unitary_liftTwo_weak hK hn hN hp hpq hcop hψ hker hperf hAe hAI hsc

theorem ggTBTorAIndUFourTwo_holds : GGTBTorAIndUFourTwo := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  exact ⟨K, i1, i2, hK, hQ', ggTorusTorW_unitary_liftTwo (n := 1) (N := 3) hK le_rfl le_rfl
    Nat.prime_three (by norm_num) (by norm_num)⟩

theorem ggTBTorAInd_holds : GGTBTorAInd :=
  ggTBTorAInd_of_uThree (ggTBTorAIndUThree_of_uFourTwo ggTBTorAIndUFourTwo_holds)

end Certificates

end CFSG.StandardType

end
