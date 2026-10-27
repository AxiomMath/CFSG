module

public import CFSG.Quasithin.Vol2.Ch11SecO11C
public import CFSG.Quasithin.Vol2.Ch11SecQ9aShA
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListD4
public import CFSG.LieType.Chevalley.TrialityExactFiniteOrder

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.O11

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.Vol2Native.A312L


theorem seven_dvd_card_parab {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hK : Nat.card K = 4 ^ 3) (hσ : ∀ c, σ c = c ^ 4)
    (hU : IsPGroup 2 ↥(graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom))
    {a : Fin TwistTag.D4.foldedTag.rank} (ha : (TwistTag.D4.orbit a).card = 3) :
    7 ∣ Nat.card ↥(perfectCore ((graphFixedParabolic TwistTag.D4 K σ.toRingHom {a}).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) := by
  have hK3 : Nat.card K = 2 ^ 6 := by rw [hK]; norm_num
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by norm_num) hK3
  have hL : Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom a) = 64 := by
    rw [card_orbitField_D4_orientation (ℓ := 2) (f := 2) Nat.prime_two (by norm_num)
      (by rw [hK]; norm_num) (r := 1) (Or.inl rfl) (fun c => by rw [pow_one]; exact hσ c), ha]
    norm_num
  obtain ⟨g, hg, -⟩ := exists_levi_hom_fixed σ a hU
    (exists_finset_card_four (by rw [hL]; norm_num))
  refine dvd_trans ?_ (Subgroup.card_dvd_of_surjective hg)
  have : Fintype ↥(orbitField TwistTag.D4 K σ.toRingHom a) := Fintype.ofFinite _
  have hL' : Fintype.card ↥(orbitField TwistTag.D4 K σ.toRingHom a) = 64 := by
    rw [← Nat.card_eq_fintype_card, hL]
  rw [Matrix.card_SL_field, Fin.prod_univ_two, hL']
  norm_num

theorem l24Unique_3d4 {Q : Type} [Group Q] [Finite Q] (hQ : Is3D4 2 2 Q) {S : Subgroup Q}
    (hS : QuasithinUnique.IsSylowTwoOf S ⊤) : L24Unique S := by
  obtain ⟨K, _, _, σ, φ, hK, hσ, hU, hres, -⟩ := even_rank_two_residual_triality hQ hS
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hS2 : IsPGroup 2 S := hS.2.1
  have hU2 : IsPGroup 2 ↥(graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) := by
    have h1 : IsPGroup 2 ↥(S.map φ.toMonoidHom) := hS2.map _
    rw [hU] at h1
    exact h1.of_equiv
      (Subgroup.subgroupOfEquivOfLe (graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _))
  obtain ⟨j₀, hj₀⟩ := d4Index_surjective ⟨0, by decide⟩
  have h3 : (TwistTag.D4.orbit (d4Index j₀)).card = 3 := by rw [hj₀]; decide
  have h7 := seven_dvd_card_parab σ (by rw [hK]; norm_num) (fun c => by rw [hσ]; norm_num) hU2 h3
  set P : Fin 2 → Subgroup Q := fun j =>
    ((graphFixedParabolic TwistTag.D4 K σ.toRingHom {d4Index j}).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.symm.toMonoidHom with hP
  have h7Q : 7 ∣ Nat.card ↥(perfectCore (P j₀)) := by
    rw [← dInf_eq_perfectCore, hP, dInf_map_equiv, dInf_eq_perfectCore,
      Subgroup.card_map_of_injective φ.symm.injective]
    exact h7
  obtain ⟨-, -, -, -, hC2, -⟩ := hres
  have key : ∀ B : Subgroup Q, IsL24Sub S B → ∃ j, j ≠ j₀ ∧ B = perfectCore (P j) := by
    intro B hB
    obtain ⟨a, ha⟩ := card_of_l24 hB
    have h7B : ¬ 7 ∣ Nat.card B := by
      rw [ha]
      intro h
      rcases (Nat.Prime.dvd_mul (by norm_num)).mp h with h | h
      · norm_num at h
      · have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
          ((by norm_num : Nat.Prime 7).dvd_of_dvd_pow h)
        norm_num at this
    have hcore : perfectCore (B ⊔ S) = B := eq_perfectCore_sup hS2 hB
    by_cases htop : B ⊔ S = ⊤
    · exfalso
      apply h7B
      have hle : perfectCore (P j₀) ≤ B := by
        rw [← hcore, htop]
        exact perfectCore_mono le_top
      exact h7Q.trans (Subgroup.card_dvd_of_le hle)
    · have hns : ¬ Group.IsSolvable ↥(B ⊔ S) := fun hsol =>
        hB.1 (C11P9A.eq_bot_of_perfect_of_le_solvable hB.2.1 le_sup_left hsol)
      obtain ⟨j, -, hdj⟩ := hC2 (B ⊔ S) le_sup_right htop hns
      rw [dInf_eq_perfectCore, dInf_eq_perfectCore, hcore] at hdj
      refine ⟨j, fun hj => h7B ?_, hdj⟩
      rw [hdj, hj]
      exact h7Q
  have fin2 : ∀ a b c : Fin 2, b ≠ a → c ≠ a → b = c := by decide
  intro B₁ B₂ h₁ h₂
  obtain ⟨j₁, hj₁, e₁⟩ := key B₁ h₁
  obtain ⟨j₂, hj₂, e₂⟩ := key B₂ h₂
  rw [e₁, e₂, fin2 j₀ j₁ j₂ hj₁ hj₂]

end CFSG.Quasithin.Vol2.Ch11.SecS.O11
