module

public import CFSG.LocalAnalysis.StandardType.GGTorDNsWitness
public import CFSG.LocalAnalysis.StandardType.GGTorusTorLiftTwo
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusTransferCore
public import CFSG.LocalAnalysis.StandardType.GGTBTorTransport
public import CFSG.LocalAnalysis.StandardType.GGTBTorRest
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenOrth

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open TorDNs
open CFSG.RankThree.Classical2 (orthDerived)

theorem ggTorusTorW_orthDerived {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {p N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) (hdim : Module.finrank K V = 2 * N) (hN : 4 ≤ N)
    (htype : CFSG.GroupTheory.WeirSylow.IsPlusType Q ↔ Even N) {R : Type} [Group R]
    (θ : R ≃* ↥(orthDerived Q)) (hcp : ∀ q : ℕ, q.Prime → q ≠ 2 → GGCenterPrime q R) (r : ℕ) :
    GGTorusTorW p r (Nat.card K + 1) N (CartanMatrix.D N) (ggCoxeterMatrixD N) R
      (LargeEvenInnSet R) := by
  classical
  intro L' _ _ ψ A hTB
  obtain ⟨hψ, hker, hperf, hAe, hAI, -, -, hsc⟩ := hTB
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  have h2q : 2 ∣ Nat.card K := by
    have := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    exact (CharP.cast_eq_zero_iff K 2 _).mp (FiniteField.cast_card_eq_zero K)
  have hm : Odd (Nat.card K + 1) := (even_iff_two_dvd.mpr h2q).add_one
  have hZΩ : Subgroup.center ↥(orthDerived Q) = ⊥ :=
    (OrthRestOdd.orthDerived_facts Q hQ (by omega)).2.1
  have hZR : Subgroup.center R = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have h1 : θ z ∈ Subgroup.center ↥(orthDerived Q) := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      obtain ⟨y, rfl⟩ := θ.surjective g
      rw [← map_mul, ← map_mul, hz y]
    rw [hZΩ, Subgroup.mem_bot] at h1
    exact θ.injective (h1.trans (map_one θ).symm)
  have h2 : IsPGroup 2 ψ.ker := by
    have hZ : IsPGroup 2 (Subgroup.center L') := by
      refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_)
      intro q hq hqd
      by_contra hq2
      exact hcp q hq hq2 L' ψ hψ hker hperf hqd
    exact hZ.to_le hker
  obtain ⟨Λ, -, -, hΛmap, hAΛ, hER, -, hERsc⟩ :=
    TwE6TB.exists_innerModel hp hZR (fun _ hφ _ => hφ)
      (hcp p hp hp2) ψ hψ hker hperf hAe hAI hsc
  let ER := A.comap Λ
  have hAbER : TypeA.inducedSub ψ A = scalarA ER :=
    TypeA.inducedSub_eq_map_conj_of_lift hψ Λ hΛmap hAΛ
  have hAind : ∀ a ∈ A, ∃ φ : MulAut R, ∀ l, φ (ψ l) = ψ (a l) := fun a ha => by
    obtain ⟨x, -, hx⟩ := hAI a ha
    exact ⟨x, hx⟩
  set E' := ER.map θ.toMonoidHom with hE'
  have hE'p : ∀ a ∈ E', a ^ p = 1 := by
    rintro _ ⟨s, hs, rfl⟩
    show θ s ^ p = 1
    rw [← map_pow, hER.2 s hs, map_one]
  have hE'c : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩
    show θ s * θ s' = θ s' * θ s
    rw [← map_mul, ← map_mul, TableB.IsElemAbelian.comm hER hs hs']
  have hE'max : ∀ g : ↥(orthDerived Q), (∀ a ∈ E', g * a = a * g) → g ^ p = 1 → g ∈ E' := by
    intro g hg hgp
    refine ⟨θ.symm g, ?_, θ.apply_symm_apply g⟩
    refine hERsc (θ.symm g) (fun s hs => ?_) (by rw [← map_pow, hgp, map_one])
    apply θ.injective
    simpa only [map_mul, θ.apply_symm_apply] using hg (θ s) ⟨s, hs, rfl⟩
  have hE'ea : IsElemAbelian p E' :=
    ⟨⟨⟨fun a b => Subtype.ext (hE'c a.1 a.2 b.1 b.2)⟩⟩, hE'p⟩
  obtain ⟨w₀, hw₀, hT₀, hTsc₀⟩ :=
    exists_ggTorusTorWit_omega hQ hp hp2 hpq hdim hN htype hE'ea hE'max
  have hEe : E'.map θ.symm.toMonoidHom = ER := by
    ext x
    constructor
    · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      simpa using hs
    · intro hx
      exact ⟨θ x, ⟨x, hx, rfl⟩, by simp⟩
  have hA2 : (scalarA E').map (MulAut.congr θ.symm).toMonoidHom = TypeA.inducedSub ψ A := by
    rw [hAbER, ← hEe]
    ext φ
    constructor
    · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      exact ⟨θ.symm s, ⟨s, hs, rfl⟩, (congr_conj θ.symm s).symm⟩
    · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      exact ⟨MulAut.conj s, ⟨s, hs, rfl⟩, congr_conj θ.symm s⟩
  refine ggTorusTorData_liftTwo hψ hker h2 hperf hZR hm hAind hA2 (w₀.transport θ.symm)
    (w₀.holds_transport θ.symm hw₀) ?_ ?_
  · rintro _ ⟨τ, hτ, rfl⟩
    obtain ⟨s, hs, rfl⟩ := hT₀ τ hτ
    exact ⟨θ.symm s, ⟨s, hs, rfl⟩, congr_conj θ.symm s⟩
  · rw [GGTorusTorWit.transport_Tsc, Subgroup.card_map_of_injective θ.symm.injective]
    exact hTsc₀

section Certificates


theorem ggTorusTorW_omegaPlus_nonsplit {K : Type} [Field K] [Finite K] [CharP K 2] {p N : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) (hN : 4 ≤ N) (hN2 : Even N)
    (r : ℕ) :
    GGTorusTorW p r (Nat.card K + 1) N (CartanMatrix.D N) (ggCoxeterMatrixD N)
      (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K N))) (LargeEvenInnSet _) :=
  ggTorusTorW_orthDerived (TableBOrth.nondegenerate_qPlusForm N) hp hp2 hpq
    (by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]; ring) hN
    ⟨fun _ => hN2, fun _ => CFSG.GroupTheory.WeirSylow.isPlusType_quadPlus K N⟩
    (OrthTorus.rPlusEquiv K (by omega))
    (fun _ hq hq2 => CorFourTwoOpen.ggCenterPrime_omegaPlus hq hq2 (by omega)) r

theorem ggTorusTorW_omegaMinus_nonsplit {K : Type} [Field K] [Finite K] [CharP K 2] {p N : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) (hN : 4 ≤ N) (hN2 : Odd N)
    {b c : K} (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (r : ℕ) :
    GGTorusTorW p r (Nat.card K + 1) N (CartanMatrix.D N) (ggCoxeterMatrixD N)
      (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (N - 1) b c))) (LargeEvenInnSet _) := by
  have hdim : Module.finrank K (LargeEvenMinusIdx (N - 1) → K) = 2 * N := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    omega
  have htype : CFSG.GroupTheory.WeirSylow.IsPlusType (TableBOrth.qMinusForm K (N - 1) b c) ↔
      Even N := by
    refine ⟨fun h => absurd ((CFSG.GroupTheory.WeirSylow.isPlusType_congr
      (TableBOrth.qMinusIsometry (N - 1) b c)).mp h)
        (CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus (by omega) hbc),
      fun h => absurd h (Nat.not_even_iff_odd.mpr hN2)⟩
  exact ggTorusTorW_orthDerived (TableBOrth.nondegenerate_qMinusForm (N - 1) hbc) hp hp2 hpq hdim
    hN htype (OrthTorus.rMinusEquiv K (N - 1) b c)
    (fun _ hq hq2 => CorFourTwoOpen.ggCenterPrime_omegaMinus hq hq2 (by omega) hbc) r

theorem ggTBTorDHigh_nonsplit : GGTBTorDHighNonsplit := by
  intro p hp hp2 lab _ hrank hpq hrow
  obtain ⟨tag, l, f⟩ := lab
  dsimp only at hrank hrow hpq ⊢
  have hq : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hn1 : ¬ p ∣ 2 ^ f - 1 := by
    intro h1
    have h3 : p ∣ (2 ^ f + 1) - (2 ^ f - 1) := Nat.dvd_sub hpq h1
    rw [show (2 ^ f + 1) - (2 ^ f - 1) = 2 by omega] at h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)
  have hM : ggTorMpm p ⟨tag, l, f⟩ = 2 ^ f + 1 := by
    unfold ggTorMpm
    dsimp only
    rw [ite_eq_right hn1]
  rw [hM]
  intro Q hQ
  rcases hrow with ⟨rfl, hev⟩ | ⟨rfl, hodd⟩
  · have hl3 : l ≠ 3 := by omega
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_right hl3] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hQK⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpK : p ∣ Nat.card K + 1 := by rw [hK]; exact hpq
    have h := ggTorusTorW_omegaPlus_nonsplit hp hp2 hpK hrank hev (l - ggTorEnn p ⟨.D, l, f⟩)
    rw [hK] at h
    exact ⟨K, i1, i2, hK, hQK, h⟩
  · have hl2 : l ≠ 2 := by omega
    have hl3 : l ≠ 3 := by omega
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_right hl2, ite_eq_right hl3] at hQ ⊢
    obtain ⟨K, i1, i2, hK, b, c, hbc, hQK⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpK : p ∣ Nat.card K + 1 := by rw [hK]; exact hpq
    have h := ggTorusTorW_omegaMinus_nonsplit hp hp2 hpK hrank hodd hbc
      (l - ggTorEnn p ⟨.twD, l, f⟩)
    rw [hK] at h
    exact ⟨K, i1, i2, hK, b, c, hbc, hQK, h⟩

end Certificates

end CFSG.StandardType

end
