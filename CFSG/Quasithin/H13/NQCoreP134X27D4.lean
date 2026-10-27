module

public import CFSG.Quasithin.H13.NQCoreP134X27Borel
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieD4Trans
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverBase

public section

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
  CFSG.LieType.BorelTits CFSG.Quasithin.F134 CFSG.Quasithin.F134.LieD4 CFSG.Quasithin.H13.NQCore

namespace CFSG.Quasithin.H13.NQCore.X27D4

theorem false_of_dvd_of_dvd_mul_pow {p a n d B : ℕ} (hp : p.Prime)
    (hne : ∀ m : ℕ, 2 ^ m + 1 ≠ p ^ a)
    (hBp : ¬ p ∣ B) (h1 : 1 + (2 ^ n) ^ d ∣ p ^ a) (h2 : p ^ a ∣ B * (1 + (2 ^ n) ^ d)) :
    False := by
  have hcop : Nat.Coprime (p ^ a) B :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).2 hBp)
  have h3 : p ^ a ∣ 1 + (2 ^ n) ^ d := hcop.dvd_of_dvd_mul_left h2
  have h4 : 1 + (2 ^ n) ^ d = p ^ a := Nat.dvd_antisymm h1 h3
  refine hne (n * d) ?_
  rw [pow_mul, ← h4]
  omega

variable {K : Type} [Field K]

theorem le_graphFixedRootBorel_of_card_eq_pow
    [Finite K] (σ : K ≃+* K) {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 3) (hσc : ∀ c, σ c = c ^ (2 ^ n)) {p a : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hne : ∀ m : ℕ, 2 ^ m + 1 ≠ p ^ a) {Q H : Subgroup (ModGL TwistTag.D4.tag K)}
    (hBQ : graphFixedRootBorel TwistTag.D4 K σ.toRingHom ≤ Q)
    (hQC : Q ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hQ : Q ≠ graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (hHQ : H ≤ Q)
    (hUH : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤ H)
    (hH : Nat.card H = p ^ a * Nat.card (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)) :
    H ≤ graphFixedRootBorel TwistTag.D4 K σ.toRingHom := by
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hK3 : Nat.card K = 2 ^ (3 * n) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK3
  have hσ : Function.Surjective σ.toRingHom := σ.surjective
  obtain ⟨b, hQb⟩ := D4.exists_le_graphFixedParabolic_singleton σ hBQ hQC hQ
  have hHb := hHQ.trans hQb
  have hUrel : (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).relIndex H = p ^ a := by
    have h := Subgroup.relIndex_mul_card (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) H
    rw [inf_eq_left.2 hUH, hH] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hBdvd : (graphFixedRootBorel TwistTag.D4 K σ.toRingHom).relIndex H ∣ p ^ a :=
    hUrel ▸ Subgroup.relIndex_dvd_of_le_left H graphFixedPosUnipotent_le_graphFixedRootBorel
  rcases le_or_relIndex_eq hσ hUH hHb with hHB | hrel
  · exact hHB
  exfalso
  rw [hrel, card_graphFixedInversionUnipotent_D4 σ hn hK hσc b] at hBdvd
  have hd : (TwistTag.D4.orbit b).card = 1 ∨ (TwistTag.D4.orbit b).card = 3 := by
    have : ∀ c : Fin TwistTag.D4.foldedTag.rank,
        (TwistTag.D4.orbit c).card = 1 ∨ (TwistTag.D4.orbit c).card = 3 := by decide
    exact this b
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 hBdvd
  have hi0 : i ≠ 0 := by
    rintro rfl
    simp at hi
  have hpd : p ∣ 1 + (2 ^ n) ^ (TwistTag.D4.orbit b).card := hi ▸ dvd_pow_self p hi0
  have hpK : ¬ p ∣ Nat.card K - 1 := by
    rw [hK]
    exact D4.not_dvd_pow_three_sub_one hp hp2 (Nat.one_le_two_pow) hd hpd
  have hB := D4.not_dvd_card_graphFixedRootBorel (t := TwistTag.D4) hσ hp hp2 hpK
  have hPb := card_graphFixedParabolic_singleton hσ b
  rw [card_graphFixedInversionUnipotent_D4 σ hn hK hσc b] at hPb
  have hPdvd : p ^ a ∣ Nat.card (graphFixedParabolic TwistTag.D4 K σ.toRingHom {b}) :=
    (Dvd.intro _ hH.symm).trans (Subgroup.card_dvd_of_le hHb)
  rw [hPb] at hPdvd
  exact false_of_dvd_of_dvd_mul_pow hp hne hB hBdvd hPdvd

theorem le_normalizer_of_card_eq_pow
    {X : Type} [Group X] [Finite X] {n : ℕ}
    (hX : ChevalleyExceptionalModel X .trialityD4 2 n) (U : Sylow 2 X) {p a : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (ha : a ≤ 3) (hne : ∀ m : ℕ, 2 ^ m + 1 ≠ p ^ a) {H : Subgroup X}
    (hUH : (U : Subgroup X) ≤ H)
    (hH : Nat.card H = p ^ a * Nat.card (U : Subgroup X)) :
    H ≤ Subgroup.normalizer ((U : Subgroup X) : Set X) := by
  obtain ⟨hn, K, _, _, σ, hK, hσc, e, he⟩ := LieD4.exists_mulEquiv_map_eq hX U
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hUC := graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  set φ : X →* ModGL TwistTag.D4.tag K :=
    (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype.comp e.toMonoidHom with hφ
  have hφi : Function.Injective φ := Subtype.val_injective.comp e.injective
  have hφr : (⊤ : Subgroup X).map φ = graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
    rw [hφ, ← Subgroup.map_map, Subgroup.map_top_of_surjective _ e.surjective, Subgroup.map_top,
      Subgroup.range_subtype]
  have hφU : (U : Subgroup X).map φ = graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom := by
    rw [hφ, ← Subgroup.map_map, he, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  obtain ⟨E, hEU, hE2, hE16⟩ := D4.exists_isElemAbelian_le_sylow hX U
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 U.isPGroup'
  obtain ⟨Q, hQ, hHQ, hNQ⟩ := S5.exists_proper_overgroup (holds_of_chevalleyExceptionalModel hX)
    (LieF4.isSylowOf_of_sylow U le_top) hUH (hEU.trans hUH) hE2 hE16 hp hp2 (m := m)
    (a := a) (by rw [hH, hm, mul_comm]) ha
  have hle : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤ φ.range := by
    rw [← hφU]
    exact Subgroup.map_le_range φ _
  have hNcomap : (Subgroup.normalizer (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom :
      Set (ModGL TwistTag.D4.tag K))).comap φ = Subgroup.normalizer ((U : Subgroup X) : Set X) := by
    rw [Subgroup.comap_normalizer_eq_of_le_range hle, ← hφU,
      Subgroup.comap_map_eq_self_of_injective hφi]
  have hBQ : graphFixedRootBorel TwistTag.D4 K σ.toRingHom ≤ Q.map φ := by
    intro b hb
    rw [← graphFixedRootGroup_inf_normalizer_graphFixedPosUnipotent σ.surjective] at hb
    obtain ⟨hbC, hbN⟩ := hb
    rw [← hφr] at hbC
    obtain ⟨x, -, rfl⟩ := hbC
    refine ⟨x, hNQ ?_, rfl⟩
    rw [← hNcomap]
    exact hbN
  have hHB := le_graphFixedRootBorel_of_card_eq_pow σ hn hK hσc hp hp2 hne (Q := Q.map φ)
    (H := H.map φ) hBQ
    ((Subgroup.map_le_range φ Q).trans (by rw [MonoidHom.range_eq_map, hφr]))
    (fun h => hQ (Subgroup.map_injective hφi (by rw [h, hφr]))) (Subgroup.map_mono hHQ)
    (by rw [← hφU]; exact Subgroup.map_mono hUH)
    (by rw [Subgroup.card_map_of_injective hφi, hH, ← Subgroup.card_map_of_injective hφi, hφU])
  intro x hx
  rw [← hNcomap]
  exact graphFixedRootBorel_le_normalizer_graphFixedPosUnipotent (hHB ⟨x, hx, rfl⟩)

theorem noX27Simple_d4Even
    (n : ℕ) :
    NoX27Simple fun (X : Type) [Group X] => ChevalleyExceptionalModel X .trialityD4 2 n := by
  intro A _ _ L P T hcfg h27 hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U⟩ : Nonempty (Sylow 2 ↥L) := inferInstance
  refine false_of_borel_data_x27 hcfg h27 (MulEquiv.refl ↥L) (U := (U : Subgroup ↥L))
    (B := Subgroup.normalizer ((U : Subgroup ↥L) : Set ↥L)) U.isPGroup' U.not_dvd_index ?_
    (D4.commutator_mem_of_mem_normalizer hL U)
  intro H hUH hH
  exact le_normalizer_of_card_eq_pow hL U Nat.prime_three (by norm_num) le_rfl
    two_pow_add_one_ne_27 hUH (by rw [hH]; norm_num)

theorem facts134X27_d4Even :
    ∀ f : ℕ, 1 ≤ f →
      NoX27ConfigQ fun (X : Type) [Group X] => ChevalleyExceptionalModel X .trialityD4 2 f :=
  fun f _ => noX27ConfigQ_of_noCover
    (fun _ _ _ _ e h => CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv e.symm h)
    (noX27Simple_d4Even f) fun X _ _ hX h3 h => by
      have : Group.IsPerfect X := hX.1
      exact CFSG.QuasithinUnique.Ch1.false_of_odd_cover_trivial h3 (MulEquiv.refl _)
        fun π hπ hC hodd => CFSG.SectionRank.triality_even_perfect_odd_cover_trivial h π hπ hC hodd

end CFSG.Quasithin.H13.NQCore.X27D4
