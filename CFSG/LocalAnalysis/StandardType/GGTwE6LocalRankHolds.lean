module

public import CFSG.LocalAnalysis.StandardType.GGTriD4KnownInputs
public import CFSG.LocalAnalysis.StandardType.GGTwE6LocalRankCover
import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaCenter
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryLift
import CFSG.HardMathSupport.Timmesfeld.Coordinator.ElemAbelianComplement

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.CentralExt
  CFSG.LieType.Steinberg.Minuscule

section LocalRankHolds


theorem ggTwE6LocalRankInput_holds : GGTwE6LocalRankInput := by
  intro n hn h3 K _ _ hK _ X _ _ hX θ
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ψ : X →* TwE6Delta.RecipeR K n :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hψs : Function.Surjective ψ :=
    θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center X))
  have hker : ψ.ker ≤ Subgroup.center X := by
    intro x hx
    have h1 : θ (QuotientGroup.mk x) = 1 := by
      simpa [ψ] using MonoidHom.mem_ker.mp hx
    have h2 : (QuotientGroup.mk x : X ⧸ Subgroup.center X) = 1 :=
      θ.injective (by simpa using h1)
    exact (QuotientGroup.eq_one_iff x).1 h2
  have hkerEq : ψ.ker = Subgroup.center X := by
    refine le_antisymm hker ?_
    intro z hz
    rw [MonoidHom.mem_ker]
    have hz1 : (QuotientGroup.mk z : X ⧸ Subgroup.center X) = 1 :=
      (QuotientGroup.eq_one_iff z).2 hz
    show ψ z = 1
    rw [show ψ z = θ (QuotientGroup.mk z) from rfl, hz1, map_one]
  obtain ⟨q, hq, hqk⟩ := TwE6Delta.exists_sc_surjection hn hK
  haveI : Finite (twistedE6Group 2 n) := by
    haveI : Finite (Module.End (GaloisField 2 (2 * n))
        (Fin e6Data.d →₀ GaloisField 2 (2 * n))) :=
      Module.finite_of_finite (GaloisField 2 (2 * n))
    infer_instance
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* twistedE6Group 2 n),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Nat.Coprime 2 (Nat.card π.ker) →
        ∃ s : twistedE6Group 2 n →* E, ∀ h, π (s h) = h :=
    fun E _ _ π hπ hc hcop => TwistedE6Closed.twistedE6_exists_section_of_coprime
      (k := GaloisField 2 (2 * n)) (θ := frobQ 2 n) (frobQ_frobQ 2 n hn) (p := 2) hπ hc hcop
  have hcardZ : Nat.card (Subgroup.center (twistedE6Group 2 n)) = 3 := by
    have h := (TwistedE6Closed.card_center_fixedGroup (k := GaloisField 2 (2 * n))
      (θ := frobQ 2 n) (q := 2 ^ n) (card_galoisField_two_mul 2 n hn)
      (fun c => by rw [frobQ_apply])).1
    rw [h]
    exact Nat.gcd_eq_left h3
  obtain ⟨U₀, E', hU₀, hU₀2, hE'U₀, hE'ab, hE'card⟩ :=
    TwE6Lang.exists_cover_localRank hn h3
  have hE'ker_le : Nat.card ↥(E' ⊓ q.ker) ≤ 3 := by
    calc Nat.card ↥(E' ⊓ q.ker) ≤ Nat.card q.ker := Subgroup.card_le_of_le inf_le_right
      _ ≤ Nat.card (Subgroup.center (twistedE6Group 2 n)) := Subgroup.card_le_of_le hqk
      _ = 3 := hcardZ
  have hk4 : 3 ^ 4 * Nat.card ↥(E' ⊓ q.ker) ≤ Nat.card E' := by
    rw [hE'card]
    calc 3 ^ 4 * Nat.card ↥(E' ⊓ q.ker) ≤ 3 ^ 4 * 3 := Nat.mul_le_mul_left _ hE'ker_le
      _ = 3 ^ 5 := by norm_num
  obtain ⟨E₀, hE₀E', hE₀ab, hE₀card, hE₀inf⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.exists_elemAbelian_le_inf_eq_bot
      Nat.prime_three hE'ab inf_le_left 4 hk4
  have hE₀q : E₀ ⊓ q.ker = ⊥ := by
    have h1 := hE₀inf
    rw [← inf_assoc, inf_eq_left.mpr hE₀E'] at h1
    exact h1
  have hU₀k : ¬ U₀ ≤ q.ker := by
    intro hle
    have hU₀c : U₀ ≤ Subgroup.center (twistedE6Group 2 n) := le_trans hle hqk
    have hdvd : Nat.card U₀ ∣ 3 := by
      have h := Subgroup.card_dvd_of_le hU₀c
      rwa [hcardZ] at h
    rcases IsPGroup.card_eq_or_dvd hU₀2 with h1 | h2
    · exact hU₀ (Subgroup.eq_bot_of_card_eq U₀ h1)
    · exact absurd (dvd_trans h2 hdvd) (by norm_num)
  have hEU₀ : E₀ ≤ Subgroup.normalizer (U₀ : Set (twistedE6Group 2 n)) :=
    le_trans hE₀E' hE'U₀
  obtain ⟨U, E, hU, hU2, hEU, hEab, hEcard, hEker⟩ :=
    TableBU.exists_lift_of_section q hsplit Nat.prime_three (by norm_num)
      hE₀ab hE₀q hU₀2 hU₀k hEU₀ ψ hψs hker
  exact ⟨U, hU, hU2, E, hEU, hEab, Or.inr ⟨by rw [hEcard, hE₀card], by rwa [hkerEq] at hEker⟩⟩

end LocalRankHolds

end CFSG.StandardType
