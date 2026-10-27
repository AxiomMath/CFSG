module

public import CFSG.StronglyEmbedded.BenderBorelTransport
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel

public section

namespace CFSG.Open

open CFSG.BenderSuzuki

noncomputable section

theorem fusionBenderBorel_of_regular_root
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω]
    (a : Ω) (R D : Subgroup G) (q k : ℕ)
    (hRle : R ≤ MulAction.stabilizer G a)
    (hDle : D ≤ MulAction.stabilizer G a)
    (hN : MulAction.stabilizer G a ≤ Subgroup.normalizer (R : Set G))
    (hdisjoint : R ⊓ D = ⊥)
    (hsup : R ⊔ D = MulAction.stabilizer G a)
    (hcyc : IsCyclic D) (hodd : Odd (Nat.card D))
    (hRp : IsPGroup 2 R) (heven : Even (Nat.card R))
    (hmove : ∃ g : G, g • a ≠ a)
    (hreg : ∀ b c : Ω, b ≠ a → c ≠ a → ∃! r : R, (r : G) • b = c)
    (hpow : ∀ z ∈ Subgroup.center R, z ^ 2 = 1)
    (hZcard : Nat.card (Subgroup.center R) = q)
    (hRcard : Nat.card R = q ^ k) : fusionBenderBorel G q k := by
  have hRne : R ≠ ⊥ := by
    intro h
    have hcard : Nat.card R = 1 := by rw [h]; simp
    rw [hcard] at heven
    exact (by decide : ¬ Even (1 : ℕ)) heven
  have hnormalizer : Subgroup.normalizer (R : Set G) = MulAction.stabilizer G a :=
    normalizer_eq_stabilizer_of_regular_compl R a hRle hRne hreg hN
  obtain ⟨P, hP⟩ := exists_sylow_map_eq_of_normal_complement
    hRle hDle hN hdisjoint hsup hRp hodd.not_two_dvd_nat
  obtain ⟨S, hS⟩ := exists_sylow_map_eq_of_normalizer_le P (by
    rw [hP, hnormalizer])
  have hSR : (S : Subgroup G) = R := hS.trans hP
  apply fusionBenderBorel_of_one_sylow S
  have hNS : Subgroup.normalizer ((S : Subgroup G) : Set G) =
      MulAction.stabilizer G a := by rw [hSR]; exact hnormalizer
  have hregS : ∀ b c : Ω, b ≠ a → c ≠ a → ∃! s : S, (s : G) • b = c := by
    intro b c hb hc
    let e : (S : Subgroup G) ≃* R := MulEquiv.subgroupCongr hSR
    obtain ⟨r, hr, huniq⟩ := hreg b c hb hc
    refine ⟨e.symm r, ?_, ?_⟩
    · change (e.symm r : G) • b = c
      simp only [e, MulEquiv.subgroupCongr_symm_apply]
      exact hr
    · intro s hs
      apply e.injective
      have he : e s = r := huniq (e s) (by
        change (e s : G) • b = c
        simp only [e, MulEquiv.subgroupCongr_apply]
        exact hs)
      simpa using he
  have hSE := fusionStronglyEmbedded_of_sylow_regular_compl S a hNS hmove
    (hSR ▸ heven) hregS
  change fusionBenderSubgroupData (S : Subgroup G) q k
  have hdata : fusionBenderSubgroupData R q k :=
    ⟨by simpa only [hSR] using hSE,
      ⟨D, hcyc, hodd, hdisjoint, hsup.trans hnormalizer.symm⟩,
      hpow, hZcard, hRcard⟩
  rw [hSR]
  exact hdata

end

end CFSG.Open
