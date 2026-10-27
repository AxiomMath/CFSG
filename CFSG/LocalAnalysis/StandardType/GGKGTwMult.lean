module

public import CFSG.Open.StatedDefs
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate10010
public import Certificates.Certificate10011
import CFSG.LieType.Steinberg.CentralExt.SUCentrallyClosed
import CFSG.LieType.Steinberg.CentralExt.SL2CentrallyClosed
import CFSG.LocalAnalysis.SectionRank.EvenCover.Unitary
import CFSG.LieType.Universal.Unitary.Comparison
import CFSG.LieType.Multipliers.U42
public import CFSG.LieType.Multipliers.U42Bridge

public section

namespace CFSG.StandardType.KGL

open CFSG CFSG.Open

private theorem center_statedSU_four_eq_bot {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) :
    Subgroup.center (StatedSU 4 (2 ^ f) F) = ⊥ ∧
      (StatedScalars (Fin 4) F).subgroupOf (StatedSU 4 (2 ^ f) F) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (F := F) (p := 2) (f := f) (n := 4) hF (by norm_num) (by simp)).2
  have hscal := CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedSU_four_eq_bot
    (K := F) (2 ^ f)
  exact ⟨h.trans hscal, hscal⟩

private theorem center_le_ker_of_center_eq_bot {G H : Type} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (hcenter : Subgroup.center H = ⊥) :
    Subgroup.center G ≤ f.ker := by
  intro z hz
  rw [MonoidHom.mem_ker]
  have hle : Subgroup.map f (Subgroup.center G) ≤ Subgroup.center H :=
    Subgroup.map_center_le_center (f := f) hf
  have hmem : f z ∈ Subgroup.map f (Subgroup.center G) := ⟨z, hz, rfl⟩
  have : f z ∈ (⊥ : Subgroup H) := by rw [← hcenter]; exact hle hmem
  simpa using this

private theorem card_center_dvd_griess {S Q : Type} [Group S] [Group Q] (hQ : Group.IsPerfect Q)
    (e : Q ⧸ Subgroup.center Q ≃* S) :
    Nat.card (Subgroup.center Q) ∣ Nat.card (griessHopfMultiplier S) := by
  have := hQ
  let q : Q →* S := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = Subgroup.center Q := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' (Subgroup.center Q) x) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hmap := CFSG.RankThree.PerfectCover.map_hopfMultiplier_hopfLift q hq hker.le
  rw [Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess S).toEquiv, ← hker,
    ← hmap]
  exact Subgroup.card_map_dvd (H := CFSG.RankThree.PerfectCover.hopfMultiplier S)
    (CFSG.RankThree.PerfectCover.hopfLift q hq hker.le)

theorem kgMult_statedSU_four
    {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hf : 1 ≤ f)
    (hF : Nat.card F = (2 ^ f) ^ 2)
    (N : Type) [Group N] [Finite N] (π : N →* StatedSU 4 (2 ^ f) F)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center N) (hperf : commutator N = ⊤) :
    IsCyclic (Subgroup.center N) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcenterA, hscal⟩ := center_statedSU_four_eq_bot hF
  have hker_eq : π.ker = Subgroup.center N :=
    le_antisymm hker (center_le_ker_of_center_eq_bot π hπ hcenterA)
  rcases Nat.lt_or_ge f 2 with hflt | hfge
  ·
    have hf1 : f = 1 := by omega
    subst hf1
    let X := StatedProj (StatedSU 4 (2 ^ 1) F)
    have hstar : StatedSU 4 (2 ^ 1) F ≃* X :=
      ((QuotientGroup.quotientMulEquivOfEq hscal).trans QuotientGroup.quotientBot).symm
    have hX : CFSG.Blueprint.LieModel X .PSU 4 2 1 :=
      Or.inl ⟨by decide, ⟨Nat.prime_two, le_rfl, by norm_num, by decide⟩, F, inferInstance,
        inferInstance, hF, ⟨MulEquiv.refl X⟩⟩
    obtain ⟨-, hM⟩ := CFSG.LieType.Multipliers.U42.multiplier_PSU_four_two X hX
    obtain ⟨eM⟩ := hM
    have hcardM : Nat.card (griessHopfMultiplier X) = 2 := by
      rw [Nat.card_congr eM.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
        ZMod.card]
    have eQuot : N ⧸ Subgroup.center N ≃* X :=
      (QuotientGroup.quotientMulEquivOfEq hker_eq).symm.trans
        ((QuotientGroup.quotientKerEquivOfSurjective π hπ).trans hstar)
    have hdvd : Nat.card (Subgroup.center N) ∣ Nat.card (griessHopfMultiplier X) :=
      card_center_dvd_griess (S := X) (Q := N) ⟨hperf⟩ eQuot
    rw [hcardM] at hdvd
    exact isCyclic_of_card_dvd_prime hdvd
  ·
    have hq : 4 ≤ 2 ^ f := by
      have hle := Nat.pow_le_pow_right (by norm_num : 0 < 2) hfge
      norm_num at hle
      exact hle
    let e := CFSG.LieType.Universal.Unitary.equivStatedSU (F := F) (p := 2) (f := f) hF 4
    let π' : N →*
        CFSG.LieType.Universal.Unitary.SU
          (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) 4 :=
      e.symm.toMonoidHom.comp π
    have hπ' : Function.Surjective π' := e.symm.surjective.comp hπ
    have hker' : π'.ker = π.ker :=
      MonoidHom.ker_comp_of_injective π e.symm.toMonoidHom e.symm.injective
    have hcen' : π'.ker ≤ Subgroup.center N := by rw [hker']; exact hker
    obtain ⟨s, hs⟩ := CFSG.LieType.Steinberg.CentralExt.SUClosed.su_exists_section_of_central
      (F := F) (p := 2) (f := f) hF (n := 4) ⟨2, by norm_num⟩ le_rfl hq hπ' hcen'
    haveI : Group.IsPerfect N := ⟨hperf⟩
    have hbot : π'.ker = ⊥ :=
      CFSG.LieType.Steinberg.CentralExt.SL2Closed.ker_eq_bot_of_section π' hcen' s hs
    have hkerbot : π.ker = ⊥ := by rw [← hker', hbot]
    have hcenterbot : Subgroup.center N = ⊥ := by rw [← hker_eq, hkerbot]
    rw [hcenterbot]
    exact isCyclic_of_subsingleton

end CFSG.StandardType.KGL

end
