module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModSecOrthNat
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.IrredClassification

public section

namespace CFSG.Quasithin.F53Mod

open CFSG.Open CFSG.LieType.BorelTits Equiv

variable {G : Type} [Group G] [Finite G]

theorem chiefStep_orth_or_nat {H U L N : Subgroup G} (hq : Nonempty (OTwoQuot H ≃* Perm (Fin 5)))
    (hU : U ≤ pCoreOf 2 H) (hstep : IsChiefStep H U L N) (hnc : ¬ IsCentralStep H L N) :
    cSecIn H L N = pCoreOf 2 H ∧ (IsOrthSec H L N ∨ IsNatSec H L N) :=
  chiefStep_orth_or_nat_of_classification
    (fun M hM hnt => model5_irred_classification M hM hnt) hq hU hstep hnc

@[expose] def IsNatOrOrthMod (X V C : Subgroup G) : Prop :=
  IsChiefStep X V C V ∧ C.relIndex V = 16

theorem card_le_two_of_irred_trivial {n : ℕ} {M : Model n} (hirr : M.IsIrred)
    (htriv : ∀ σ w, M.act σ w = w) : Nat.card M.W ≤ 2 := by
  obtain ⟨⟨w, hw⟩, hirr⟩ := hirr
  have hinv : IsInvSub M ⊤ (Subgroup.zpowers w) := by
    intro b _ u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    show M.act b (w ^ k) ∈ _
    rw [map_zpow, htriv]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers w) k
  have htop : Subgroup.zpowers w = ⊤ := by
    rcases hirr _ hinv with h | h
    · exact absurd (Subgroup.eq_bot_iff_forall _ |>.mp h w (Subgroup.mem_zpowers w)) hw
    · exact h
  have h1 : Nat.card (Subgroup.zpowers w) = orderOf w := Nat.card_zpowers w
  have h2 : Nat.card (Subgroup.zpowers w) = Nat.card M.W := by
    rw [htop]; exact Nat.card_congr (Equiv.Set.univ _)
  have h3 : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact M.sq w)
  rw [← h2, h1]
  exact Nat.le_of_dvd (by norm_num) h3

theorem isNatOrOrthMod_iff {X V C : Subgroup G} (hq : Nonempty (OTwoQuot X ≃* Perm (Fin 5)))
    (hQ : pCoreOf 2 X ≤ cSecIn X C V) (hsec : IsSec X C V) :
    IsNatOrOrthMod X V C ↔ IsOrthSec X C V ∨ IsNatSec X C V := by
  constructor
  · rintro ⟨hstep, hcard⟩
    obtain ⟨φ, hφs, hφk⟩ := exists_toPerm_of_quot hq
    have hk : φ.ker ≤ (cSecIn X C V).subgroupOf X := fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hQ ((hφk x).mp hx))
    have hirr := secModule_isIrred_of_isChiefStep hsec φ hφs hk hstep
    have hc : Nat.card (secModule hsec φ hφs hk).W = 16 :=
      (natCard_secModule hsec φ hφs hk).trans hcard
    have hnt : ∃ σ w, (secModule hsec φ hφs hk).act σ w ≠ w := by
      by_contra hall
      push Not at hall
      have := card_le_two_of_irred_trivial hirr hall
      omega
    rcases model5_irred_classification _ hirr hnt with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · have hf := (secModule_faithful_iff hsec φ hφs hk).mp (Model.Faithful.of_iso e orth_faithful)
      exact Or.inl (isModelSec_of_iso hsec φ hφs (le_antisymm hk hf) e.symm)
    · have hf := (secModule_faithful_iff hsec φ hφs hk).mp (Model.Faithful.of_iso e nat_faithful)
      exact Or.inr (isModelSec_of_iso hsec φ hφs (le_antisymm hk hf) e.symm)
  · intro h
    have key : ∀ {M : Model 5}, M.IsIrred → Nat.card M.W = 16 → IsModelSec M X C V →
        IsNatOrOrthMod X V C := by
      intro M hM hMc hMs
      obtain ⟨hN, θ, β, hθ, hker, hβ⟩ := hMs
      obtain ⟨e⟩ := exists_iso_of_isModelSec hsec θ hθ hker hβ
      have hirr := hM.of_iso e
      have hnorm : IsNormalIn X V V := ⟨le_rfl, fun g hg x hx => (Subgroup.mem_normalizer_iff.mp (hsec.normN hg) x).mp hx⟩
      have hnormC : IsNormalIn X V C := ⟨hsec.le, fun g hg x hx => hsec.conj_mem_L hg hx⟩
      refine ⟨isChiefStep_of_secModule_isIrred hsec θ hθ hker.le hnorm hnormC hirr, ?_⟩
      rw [← natCard_secModule hsec θ hθ hker.le, ← e.card_eq]
      exact hMc
    rcases h with h | h
    · exact key orth_isIrred card_orth h
    · exact key nat_isIrred card_nat h

end CFSG.Quasithin.F53Mod
