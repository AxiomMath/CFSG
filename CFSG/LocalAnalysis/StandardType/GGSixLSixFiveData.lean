module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveRoot
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneRestSeven

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

open scoped commutatorElement

section PerE

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ggCentralizer_le_normalizer_zpowers (r : G) :
    Subgroup.centralizer ({r} : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers r : Set G) := by
  intro g hg
  refine Subgroup.centralizer_le_normalizer _ ?_
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  exact hg

omit [Finite G] in
theorem ggLe_centralizer_zpowers {Q : Subgroup G} {r : G}
    (hQ : Q ≤ Subgroup.centralizer ({r} : Set G)) :
    Q ≤ Subgroup.centralizer (Subgroup.zpowers r : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  exact hQ

@[expose] def ggCommZpowersSub (P Q : Subgroup G) (r : G)
    (hP : P ≤ Subgroup.centralizer ({r} : Set G)) : Subgroup G where
  carrier := {b | b ∈ P ∧ ∀ a ∈ Q, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.zpowers r}
  one_mem' := ⟨P.one_mem, fun a _ => by simp⟩
  mul_mem' := by
    rintro b c ⟨hbP, hb⟩ ⟨hcP, hc⟩
    refine ⟨P.mul_mem hbP hcP, fun a ha => ?_⟩
    have hbr : ∀ z ∈ Subgroup.zpowers r, b * z * b⁻¹ = z := by
      intro z hz
      have hbz : b ∈ Subgroup.centralizer (Subgroup.zpowers r : Set G) :=
        ggLe_centralizer_zpowers hP hbP
      rw [Subgroup.mem_centralizer_iff] at hbz
      rw [← hbz z hz, mul_inv_cancel_right]
    have h1 := hb a ha
    have h2 := hc a ha
    have heq : a * (b * c) * a⁻¹ * (b * c)⁻¹ =
        (a * b * a⁻¹ * b⁻¹) * (b * (a * c * a⁻¹ * c⁻¹) * b⁻¹) := by group
    rw [heq, hbr _ h2]
    exact Subgroup.mul_mem _ h1 h2
  inv_mem' := by
    rintro b ⟨hbP, hb⟩
    refine ⟨P.inv_mem hbP, fun a ha => ?_⟩
    have hbz : b⁻¹ ∈ Subgroup.centralizer (Subgroup.zpowers r : Set G) :=
      ggLe_centralizer_zpowers hP (P.inv_mem hbP)
    rw [Subgroup.mem_centralizer_iff] at hbz
    have h1 := hb a ha
    have heq : a * b⁻¹ * a⁻¹ * b⁻¹⁻¹ = b⁻¹ * (a * b * a⁻¹ * b⁻¹)⁻¹ * b⁻¹⁻¹ := by group
    rw [heq, ← hbz _ (Subgroup.inv_mem _ h1), mul_inv_cancel_right]
    exact Subgroup.inv_mem _ h1

theorem ggLe_pCoreOf_two_of_perE (hG : IsCharTwoType G) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {D Q : Subgroup G} {r : G} (hr : orderOf r = 2) (hD : IsElemAbelian p D)
    (hDc : Nat.card D = p ^ 2) (hDr : D ≤ Subgroup.centralizer ({r} : Set G))
    (hQr : Q ≤ Subgroup.centralizer ({r} : Set G))
    (hQe : ∀ e ∈ D, e ≠ 1 → ∃ Qe : Subgroup G, Q ≤ Qe ∧
      (Qe ≤ pCoreOf 2 (Subgroup.centralizer ({r} : Set G)) ⊓ Subgroup.centralizer {e} ∨
        ⁅Qe, pCoreOf 2 (Subgroup.centralizer ({r} : Set G)) ⊓ Subgroup.centralizer {e}⁆ ≤
          Subgroup.zpowers r)) :
    Q ≤ pCoreOf 2 (Subgroup.centralizer ({r} : Set G)) := by
  set N := Subgroup.centralizer ({r} : Set G) with hN
  set P := pCoreOf 2 N with hPdef
  by_cases hex : ∃ e ∈ D, e ≠ 1 ∧ ∃ Qe : Subgroup G, Q ≤ Qe ∧
      Qe ≤ P ⊓ Subgroup.centralizer {e}
  · obtain ⟨e, -, -, Qe, hQQe, hQeP⟩ := hex
    exact hQQe.trans (hQeP.trans inf_le_left)
  push Not at hex
  have hPN : P ≤ N := Subgroup.map_subtype_le _
  have hcomm : ∀ e ∈ D, e ≠ 1 → P ⊓ Subgroup.centralizer {e} ≤ ggCommZpowersSub P Q r hPN := by
    intro e he he1 b hb
    obtain ⟨Qe, hQQe, hcase⟩ := hQe e he he1
    rcases hcase with h | h
    · exact absurd h (hex e he he1 Qe hQQe)
    · exact ⟨(Subgroup.mem_inf.mp hb).1, fun a ha =>
        h (Subgroup.commutator_mem_commutator (hQQe ha) hb)⟩
  have hP2 : IsPGroup 2 ↥P := ggIsPGroup_pCoreOf_two _
  have hPp : ¬ p ∣ Nat.card P := by
    obtain ⟨k, hk⟩ := hP2.exists_card_eq
    rw [hk]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
      ((Fact.out : p.Prime).dvd_of_dvd_pow h))
  have hDP : D ≤ Subgroup.normalizer (P : Set G) := fun d hd => mem_normalizer_pCoreOf (hDr hd)
  have hPS := ggLe_of_coprime_generation hD hDc hPp hDP hcomm
  have hr2 : IsPGroup 2 ↥(Subgroup.zpowers r) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hr, pow_one])
  exact le_pCoreOf_of_stability (ggCentralizer_le_normalizer_zpowers r) hr2
    (hG _ (ggIsTwoLocal_centralizer_of_orderOf_two hr)) hQr
    (fun a ha b hb => (hPS hb).2 a ha) (ggLe_centralizer_zpowers hQr)

end PerE

section RootTwoPer

variable {G : Type} [Group G] [Finite G]

@[expose] def GGSixRootTwoPerData (p : ℕ) (B : Subgroup G) (x : G) (L D J V : Subgroup G)
    (r : G) : Prop :=
  r ∈ V ∧ V ≤ J ∧ IsElemAbelian 2 V ∧ 4 ≤ Nat.card V ∧ r ∉ Subgroup.centralizer (J : Set G) ∧
    (∀ v ∈ V, v ≠ 1 → ∃ j ∈ J, v = j * r * j⁻¹) ∧
    ∀ e ∈ D, e ≠ 1 →
      V ≤ pCoreOf 2 (ggKd p B x L D J e ⊓ Subgroup.centralizer ({r} : Set G)) ∧
      (pCoreOf 2 (ggKd p B x L D J e ⊓ Subgroup.centralizer ({r} : Set G)) ≤
          pCoreOf 2 (Subgroup.centralizer ({r} : Set G)) ⊓ Subgroup.centralizer {e} ∨
        ⁅pCoreOf 2 (ggKd p B x L D J e ⊓ Subgroup.centralizer ({r} : Set G)),
          pCoreOf 2 (Subgroup.centralizer ({r} : Set G)) ⊓ Subgroup.centralizer {e}⁆ ≤
          Subgroup.zpowers r)

variable {U : Type} [Group U] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ} {ψ : U →* G}

theorem GGSixCtxV2.rootTwoData_of_perData (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ)
    {V : Subgroup G} {r : G} (hd : GGSixRootTwoPerData p B x L D J V r) :
    GGSixRootTwoData J V r := by
  obtain ⟨hrV, hVJ, hV, hV4, hrZ, hconj, hper⟩ := hd
  have : Fact p.Prime := ⟨h.prime⟩
  have hr1 : r ≠ 1 := by
    rintro rfl
    exact hrZ (Subgroup.one_mem _)
  have hr2 : orderOf r = 2 := orderOf_eq_prime (hV.2 r hrV) hr1
  have hDr : D ≤ Subgroup.centralizer ({r} : Set G) := fun e he => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (h.le_centralizer_J he) r (hVJ hrV)).symm
  have hVr : V ≤ Subgroup.centralizer ({r} : Set G) := fun v hv => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hV.1.is_comm.comm (⟨v, hv⟩ : ↥V) ⟨r, hrV⟩)
  have hVP := ggLe_pCoreOf_two_of_perE h.charTwo h.ne_two hr2 h.d_elem h.card_d hDr hVr
    fun e he he1 => ⟨_, (hper e he he1).1, (hper e he he1).2⟩
  exact ⟨hrV, hVJ, hV, hV4, hrZ, hconj, hVP⟩

end RootTwoPer

end CFSG.StandardType
