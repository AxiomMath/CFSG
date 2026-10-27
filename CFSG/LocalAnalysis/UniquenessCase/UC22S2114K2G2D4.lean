module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114L3
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114K2Tor
import CFSG.LocalAnalysis.UniquenessCase.UC22S218G2
import CFSG.LocalAnalysis.UniquenessCase.UC22S218D4
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Center
public import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21j
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
import CFSG.LieType.Multipliers.U62Sylow
import CFSG.Quasithin.Background.F9FiveStruct
import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
import CFSG.Quasithin.H13.A5S1326
import CFSG.Quasithin.H13.A5Top
import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.Blueprint.Chevalley (Tag TwistTag adjointGroup)
open CFSG.LieType.Chevalley (graphFixedRootGroup posUnipotentSub)

variable {G : Type} [Group G] [Finite G]


theorem uc22s2114_d4_not_dvd_card_sylow {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (hY : Is3D4 Y n) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) (hrn : r ∣ 2 ^ n - 1) :
    ¬ r ∣ Nat.card (Sylow 2 Y) := by
  obtain ⟨hn, K, _, _, _, σ, hσ3, hσ, hK, hk, ⟨e⟩⟩ := uc22s218_d4_exists_model hY
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Finite.of_equiv Y e.toEquiv
  rw [CFSG.ComponentClassification.AschbacherToolkit.Bender.card_sylow_eq_of_mulEquiv e 2]
  exact uc22s218_d4_model_not_dvd_card_sylow σ hn hσ3 hK hσ hk hr hr2 hr3 hrn

section G2


theorem uc22s2114_g2_not_dvd_card_sylow {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : IsG2 Y n)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) (hrn : r ∣ 2 ^ n - 1) :
    ¬ r ∣ Nat.card (Sylow 2 Y) := by
  obtain ⟨hn, K, _, _, _, hK, ⟨e⟩⟩ := uc22s218_g2_exists_model hY
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite ↥(adjointGroup Tag.G2 K) := Finite.of_equiv Y e.toEquiv
  rw [CFSG.ComponentClassification.AschbacherToolkit.Bender.card_sylow_eq_of_mulEquiv e 2]
  have hU : IsSylowTwoOf (posUnipotentSub Tag.G2 K) ⊤ :=
    CFSG.Quasithin.H13.Sec53F.G2.g2_sylow
  have hidx : ¬ 2 ∣ (posUnipotentSub Tag.G2 K).index := by
    have h := hU.2.2
    rwa [show ((posUnipotentSub Tag.G2 K).subgroupOf ⊤).index =
      (posUnipotentSub Tag.G2 K).index from Subgroup.relIndex_top_right _] at h
  let P : Sylow 2 ↥(adjointGroup Tag.G2 K) := hU.2.1.toSylow hidx
  have hP : (P : Subgroup ↥(adjointGroup Tag.G2 K)) = posUnipotentSub Tag.G2 K :=
    IsPGroup.toSylow_coe hU.2.1 hidx
  rw [Sylow.card_eq_index_normalizer P]
  have hnorm : normalizer (P : Set ↥(adjointGroup Tag.G2 K)) =
      normalizer ((posUnipotentSub Tag.G2 K : Subgroup ↥(adjointGroup Tag.G2 K)) :
        Set ↥(adjointGroup Tag.G2 K)) := by
    rw [← hP]
    rfl
  rw [hnorm]
  have hq2 : 2 ≤ Nat.card K := by
    rw [hK]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact uc22s218_g2_not_dvd_index hq2 hr hr2 hr3 (by rw [hK]; exact hrn)
    uc22s218_g2_model_index

theorem uc22s2114_false_of_isG2 {D : Data G} {Ch : Choice2011 G} (hSg : UC6S846.SigmaStd D)
    (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D) (h4 : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M)
    (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) {f : ℕ}
    (hX : IsG2 (BarInf L) f) (hf : 4 ∣ f) (hn : 4 ∣ c.n) : False := by
  have h5f : 5 ∣ 2 ^ f - 1 :=
    (by norm_num : 5 ∣ 2 ^ 4 - 1).trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hf)
  have h5n : 5 ∣ 2 ^ c.n - 1 :=
    (by norm_num : 5 ∣ 2 ^ 4 - 1).trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hn)
  have hZ : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ Nat.card (center (Bar2 L)) := fun ℓ hℓ => by
    rw [center_bar2_eq_bot_of_isG2 hL hX (by omega), card_bot]
    exact hℓ.not_dvd_one
  obtain ⟨T, hTc, hTE⟩ := uc22s218_g2_torus hX
  obtain ⟨p, hp⟩ := hSg.nonempty
  exact uc22s2114_false_of_torusFacts hSg h614 h76 h4 hH c hL (torusFacts218_G2 hX) hTc hTE
    Nat.prime_five (by norm_num) h5f h5n
    (uc22s2114_g2_not_dvd_card_sylow hX Nat.prime_five (by norm_num) (by norm_num) h5f)
    (hZ 5 Nat.prime_five) hp (hZ p (D.sig_prime p hp).1) (em _)

section D4


theorem uc22s2114_false_of_is3D4 {D : Data G} {Ch : Choice2011 G} (hSg : UC6S846.SigmaStd D)
    (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D) (h4 : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M)
    (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) {f : ℕ}
    (hX : Is3D4 (BarInf L) f) (hf : 4 ∣ f) (hn : 4 ∣ c.n) {p : ℕ} (hp : p ∈ D.sig)
    (hpf : ¬ p ∣ 2 ^ (2 * f) + 2 ^ f + 1) : False := by
  have h5f : 5 ∣ 2 ^ f - 1 :=
    (by norm_num : 5 ∣ 2 ^ 4 - 1).trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hf)
  have h5n : 5 ∣ 2 ^ c.n - 1 :=
    (by norm_num : 5 ∣ 2 ^ 4 - 1).trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hn)
  have hZ : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ Nat.card (center (Bar2 L)) := fun ℓ hℓ => by
    rw [center_bar2_eq_bot_of_is3D4 hL hX, card_bot]
    exact hℓ.not_dvd_one
  obtain ⟨T, hTc, hTE, -⟩ := uc22s218_d4_torus hX
  refine uc22s2114_false_of_torusFacts hSg h614 h76 h4 hH c hL (torusFacts218_3D4 hX) hTc hTE
    Nat.prime_five (by norm_num) h5f h5n
    (uc22s2114_d4_not_dvd_card_sylow hX Nat.prime_five (by norm_num) (by norm_num) h5f)
    (hZ 5 Nat.prime_five) hp (hZ p (D.sig_prime p hp).1) ?_
  by_cases hpq : p ∣ 2 ^ f - 1
  · exact Or.inl hpq
  · exact Or.inr ⟨hpq, hpf⟩

end D4

end G2

end CFSG.LocalAnalysis.UniquenessCase.UC22
